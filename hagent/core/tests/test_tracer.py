import functools
import json
import os
import pytest

import hagent.core.tracer as tracer
from hagent.inou.path_manager import PathManager


@pytest.fixture
def test_dir():
    """
    Returns the base YAML test directory.
    """
    return os.path.join(os.path.dirname(os.path.realpath(__file__)), 'test_data')


@pytest.fixture
def base_trace_event():
    """
    Returns an example TraceEvent.
    """
    return tracer.TraceEvent(name='t1', cat='test', ph=tracer.PhaseType.FLOW_START, ts=0, pid=0, tid=0)


@pytest.fixture
def str_base_trace_event():
    """
    Returns the string representation of the base_trace_event.
    """
    return '{"name": "t1", "cat": "test", "ph": "s", "ts": 0, "pid": 0, "tid": 0, "args": {}}'


@pytest.fixture
def clean_tracer():
    """
    Ensures that the Tracer is clean before and after each test.
    """
    tracer.Tracer.clear()
    yield
    tracer.Tracer.clear()


@pytest.fixture(autouse=True)
def setup_path_manager(tmp_path):
    """
    Sets up PathManager for tests using PathManager.configured() context manager.
    """
    with PathManager.configured(repo_dir=tmp_path, build_dir=tmp_path, cache_dir=tmp_path):
        yield


@pytest.fixture
def sample_step_sequence():
    """
    Returns a sample 2-Step sequence with a sub-event.
    """
    data = {}
    return [
        tracer.TraceEvent(
            name='step_1',
            cat='hagent.step',
            ph=tracer.PhaseType.COMPLETE,
            ts=0,
            pid=0,
            tid=0,
            args={'step_id': 0, 'data': data},
            dur=1,
        ),
        tracer.TraceEvent(
            name='step_2',
            cat='hagent.step',
            ph=tracer.PhaseType.COMPLETE,
            ts=3,
            pid=0,
            tid=1,
            args={'step_id': 1, 'data': data},
        ),
        tracer.TraceEvent(
            name='substep_1',
            cat='hagent',
            ph=tracer.PhaseType.COMPLETE,
            ts=3,
            pid=0,
            tid=1,
            args={'step_id': 0, 'data': data},
            dur=10,
        ),
    ]


class TestTracerMetaClass:
    def test_metaclass_propagate(self, clean_tracer):
        class Base(metaclass=tracer.TracerMetaClass):
            def baz(self):
                return {'result': 'base'}

        class SubClass(Base):
            def new_function(self):
                return {'result': '_subclass'}

        class SubSubClass(SubClass):
            def f(self, b: int):
                return {'result': '__subclass'}

        q = SubSubClass()
        q.f(b=5)

        # Ensure that a log event was registered, i.e. TracerMetaClass
        # was propagated through to SubClasses.
        assert len(tracer.Tracer.events) == 1

    def test_decorator_nesting(self, clean_tracer):
        def test(func):
            @functools.wraps(func)
            def wrapper(*args, **kwargs):
                result = func(*args, **kwargs)
                return result

            return wrapper

        def trace_inner(func):
            @functools.wraps(func)
            def wrapper(*args, **kwargs):
                result = func(*args, **kwargs)
                return result

            return wrapper

        class Base(metaclass=tracer.TracerMetaClass):
            def baz(self):
                return {'result': 'base'}

        class SubClass(Base):
            def new_function(self):
                return {'result': '_subclass'}

        class SubSubClass(SubClass):
            @test
            def f(self, b: int):
                return {'result': '__subclass'}

        @trace_inner
        def main():
            q = SubSubClass()
            return q.f(b=5)

        result = main()

        # Ensure that the log event belongs to SubSubClass
        # and not any parent class.
        # This also tests that the function name was not changed to another decorator.
        # This is a property of functools.wraps() moreso than the defined MetaClass.
        assert tracer.Tracer.events[0].name == 'SubSubClass::f'

        # Ensure that the result is not changed by the TracerMetaClass decorator.
        assert result == {'result': '__subclass'}


class TestTraceEvent:
    def test_init(self, base_trace_event):
        assert isinstance(base_trace_event, tracer.TraceEvent) is True

    def test_attributes(self, base_trace_event):
        assert base_trace_event.name == 't1'
        assert base_trace_event.cat == 'test'
        assert base_trace_event.ph == tracer.PhaseType.FLOW_START
        assert base_trace_event.ts == 0
        assert base_trace_event.pid == 0
        assert base_trace_event.tid == 0
        assert base_trace_event.args == {}

        e2 = tracer.TraceEvent(
            name='t1',
            cat='test',
            ph=tracer.PhaseType.FLOW_START,
            ts=0,
            pid=0,
            tid=0,
            args={'test': True},
            id=100,
            bp='e',
            dur=500,
            scope='test_event',
        )

        assert e2.args == {'test': True}
        assert e2.id == 100
        assert e2.bp == 'e'
        assert e2.dur == 500
        assert e2.scope == 'test_event'

    def test_to_json(self, base_trace_event):
        assert base_trace_event.to_json() == dict(
            name='t1', cat='test', ph=tracer.PhaseType.FLOW_START, ts=0, pid=0, tid=0, args={}
        )

    def test_to_str(self, base_trace_event, str_base_trace_event):
        # Ensure double-quotes are used for valid JSON.
        assert str(base_trace_event) == str_base_trace_event

    def test_repr(self, base_trace_event, str_base_trace_event):
        assert base_trace_event.__repr__() == str_base_trace_event


class TestTracer:
    def clear(self, clean_tracer):
        assert len(tracer.Tracer.events) == 0

    def test_log(self, base_trace_event, clean_tracer):
        tracer.Tracer.log(base_trace_event)
        assert len(tracer.Tracer.events) == 1

    def test_get_events(self, base_trace_event, clean_tracer):
        tracer.Tracer.log(base_trace_event)
        assert all([isinstance(e, dict) for e in tracer.Tracer.get_events()]) is True
        assert len(tracer.Tracer.get_events()) == 1


class TestGeneratePerfetto:
    def test_generate_simple(self, test_dir, clean_tracer):
        simple_dir = os.path.join(test_dir, 'simple')
        yaml_files = tracer.scan_for_yamls(simple_dir)
        initial, inputs, outputs = tracer.parse_yaml_files(simple_dir, yaml_files)

        tracer.Tracer.save_perfetto_trace(dependencies=(initial, inputs, outputs), filename='simple_perfetto.json')

        generated_trace = PathManager().get_cache_path('simple_perfetto.json')

        assert os.path.exists(generated_trace) is True
        with open(generated_trace, 'r', encoding='utf-8') as f:
            data = json.load(f)

        assert isinstance(data['traceEvents'], list) is True

    def test_generate_multi_input(self, test_dir, clean_tracer):
        multi_input_dir = os.path.join(test_dir, 'multi_input')
        yaml_files = tracer.scan_for_yamls(multi_input_dir)
        initial, inputs, outputs = tracer.parse_yaml_files(multi_input_dir, yaml_files)

        tracer.Tracer.save_perfetto_trace(
            dependencies=(initial, inputs, outputs), filename='multi_perfetto.json', asynchronous=True
        )

        generated_trace = PathManager().get_cache_path('multi_perfetto.json')

        assert os.path.exists(generated_trace) is True
        with open(generated_trace, 'r', encoding='utf-8') as f:
            data = json.load(f)

        assert isinstance(data['traceEvents'], list) is True
