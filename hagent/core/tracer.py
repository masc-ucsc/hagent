import functools
import glob
import json
import networkx as nx
import os
import threading
import time

from abc import ABCMeta
from enum import Enum
from typing import (
    List,
    Tuple,
)

from ruamel.yaml import YAML

# Keep everything under specific tabs in the Perfetto timeline.
HAGENT_PID = 0
HAGENT_TID = 0
LLM_PID = 1
LLM_TID = 1
METADATA_TID = 2
COST_PID = 2

def s_to_us(s: float) -> float:
    """
    Convert seconds to microseconds.
    """
    return s * 1_000_000

# https://docs.python.org/3/howto/logging-cookbook.html#implementing-structured-logging
class Encoder(json.JSONEncoder):
    def default(self, o):
        if isinstance(o, set):
            return tuple(o)
        elif isinstance(o, str):
            return o.encode('unicode_escape').decode('ascii')
        return super().default(o)

def read_yaml(input_file: str) -> dict:
    """
    Reads an input YAML file and attempts to convert it to a Python dictionary.

    Args:
        input_file: The input YAML file to convert to a dictionary.

    Returns:
        A dictionary representation of the YAML file.
        If loading fails, a dictionary with 'error' as its only key is returned instead.

    """
    try:
        yaml_obj = YAML(typ='safe')
        with open(input_file, 'r') as f:
            data = yaml_obj.load(f)
    except Exception:
        return {'error': ''}
    return data

#####################
## TRACER PERFETTO ##
#####################
class PhaseType(str, Enum):
    """
    Enum for Perfetto PhaseType constants.
    """
    DURATION_BEGIN="B"
    DURATION_END="E"
    COMPLETE="X"
    INSTANT="i"
    COUNTER="C"
    ASYNC_BEGIN="b"
    ASYNC_INSTANT="n"
    ASYNC_END="e"
    FLOW_START="s"
    FLOW_STEP="t"
    FLOW_END="f"
    SAMPLE="P"
    OBJECT_CREATE="N"
    OBEJCT_SNAPSHOT="O"
    OBJECT_DESTROY="D"
    METADATA="M"
    MEM_DUMP_GLOBAL="V"
    MEM_DUMP_PROCESS="v"
    MARK="r"
    CLOCK_SYNC="c"
    CONTEXT="(,)"

class TraceEvent:
    optional_args = ["args", "id", "bp", "dur", "scope"]
    def __init__(
            self,
            name: str,
            cat: str,
            ph: PhaseType,
            ts: int,
            pid: int,
            tid: int,
            **kwargs):
        
        if isinstance(ph, str):
            ph = PhaseType(ph)

        self.name = name
        self.cat = cat
        self.ph = ph
        self.ts = ts
        self.pid = pid
        self.tid = tid
        self.__dict__["args"] = {}
        for arg_name in kwargs:
            # Only accept valid arguments in kwargs.
            if arg_name in self.optional_args:
               self.__dict__[arg_name] = kwargs[arg_name]
        
    def to_json(self) -> dict:
        """
        Transform this event into JSON format.

        Returns:
            A dictionary repr of the TraceEvent with non-null values.
        """
        # Delete any optional values so they don't pollute the trace.
        pruned_d = {}
        for key, val in self.__dict__.items():
            if val is not None:
                pruned_d[key] = val
        pruned_d["ph"] = pruned_d["ph"].value
        return pruned_d

    def __str__(self) -> str:
        s = Encoder().encode(self.to_json())
        return s

    def __repr__(self) -> str:
        return self.__str__()

def scan_for_yamls(run_dir: str) -> List[str]:
    """
    Scans the specified directory for YAML files.
    """
    return glob.glob(f"{run_dir}/*.yaml")

def parse_yaml_files(yaml_files: List[str]) -> Tuple[set, set, set]:
    """
    Parses the YAML files for the initial hierarchy of Steps + Tool Calls.

    Args:
        yaml_files: The list of relevant YAML files to include in the trace.
    
    Returns:
        The dependencies files listed in each YAML under data['tracing']['input']
        or data['tracing']['output'].

    """
    initial = set()
    inputs = set()
    outputs = set()
    step_id = 0
    for idx, f in enumerate(yaml_files):
        data = read_yaml(f)
        if data.keys == ["error"]:
            print("Failure detected in step!")

        # If there is no 'tracing' key, it may be one of two cases.
        # - Initial input YAML
        # - Non-relevant YAML
        if data.get('tracing', None) is None:
            initial.add(os.path.basename(f))
            continue

        # Track the inputs/output YAMLs.
        for input in data['tracing']["input"]:
            inputs.add(input)
        outputs.add(data['tracing']["output"])
        # Log the Step itself.

        # Start from the __init__
        ts = data['tracing']['trace_events'][0]["ts"]
        additional_dur = data['tracing']['start'] - ts

        # Log any LLM calls made by LLM_wrap during the Step.
        if data['tracing'].get("history", None):
            for llm_call in data['tracing']["history"]:
                Tracer.log(TraceEvent(
                    name = llm_call["id"],
                    cat = "llm",
                    ph = PhaseType.COMPLETE,
                    ts = s_to_us(llm_call["created"]),
                    pid = LLM_PID,
                    tid = LLM_TID,
                    args = {
                        "step_id": step_id,
                        "data": llm_call
                    },
                    dur = s_to_us(llm_call["elapsed"]),
                ))

        # Log any TraceEvents recorded during the Step.
        if data['tracing'].get("trace_events", None):
            for trace_event in data['tracing']["trace_events"]:
                trace_event["args"]["step_id"] = step_id
                trace_event["tid"] = HAGENT_TID
                Tracer.log(TraceEvent(**trace_event))


        # Log the actual step() call.
        Tracer.log(TraceEvent(
            name = f"{data['step']}::step",
            cat = "hagent",
            ph = PhaseType.COMPLETE,
            ts = data['tracing']["start"],
            pid = HAGENT_PID,
            tid = HAGENT_TID,
            args = {
                "step_id": step_id,
            },
            dur = data['tracing']["elapsed"],
        ))

        # Then log the overarching Step execution.
        ## We add a slight offset (0.3 us) so that Flow events
        ## can pick up the overall Step instead of the __init__
        ## function.
        marker_offset = 0.3
        Tracer.log(TraceEvent(
            name = data["step"],
            cat = "hagent.step",
            ph = PhaseType.COMPLETE,
            ts = ts - marker_offset,
            pid = HAGENT_PID,
            tid = HAGENT_TID,
            args = {
                "step_id": step_id,
                "data": data
            },
            dur = data['tracing']["elapsed"] + additional_dur + marker_offset,
        ))

        step_id += 1
    return (initial, inputs, outputs)


class Tracer:
    """
    Singleton event handler for TraceEvents.
    """
    events = []
    steps = []
    id_steps = {}
    @classmethod
    def clear(cls) -> List[TraceEvent]:
        """
        Clears all internal data structures.
        """
        cls.events.clear()
        cls.steps.clear()
        cls.id_steps.clear()

    @classmethod
    def get_events(cls) -> List[TraceEvent]:
        """
        Gets the event trace.
        """
        return [event.to_json() for event in cls.events]

    @classmethod
    def log(cls, event: TraceEvent):
        """
        Add a new event.
        """
        cls.events.append(event)
        if event.cat == "hagent.step":
            cls.steps.append(event)
            cls.id_steps[event.args["step_id"]] = event
    
    @classmethod
    def get_tree_repr(cls, dependencies: Tuple[set, set, set]) -> nx.DiGraph:
        """
        Generates a NetworkX graph object to represent steps and dependencies.
        
        This uses a DiGraph, a directed graph with self loops and does not allow
        parallel edges, which would be equivalent to the same input YAML being
        present multiple times in input_files to the Step.

        - Graph nodes are indexed by YAML.

        Args:
            dependencies: Three sets of YAML files
            - initial YAML files (no dependencies)
            - input YAML files (input(s) to a Step),
            - output files (output of a Step).

        Returns:
            The graph object to manipulate.
        
        """
        initial, _, _ = dependencies
        g = nx.DiGraph()

        for step in cls.steps:
            g.add_node(
                step.args["data"]["tracing"]["output"],
                id=step.args["step_id"],
                name=step.name)
            # Map every non-initial input to the output.
            for input in step.args["data"]["tracing"]["input"]:
                if input in initial:
                    continue
                g.add_edge(input, step.args["data"]["tracing"]["output"])
        
        return g
    
    @classmethod
    def get_step_from_yaml(cls, g: nx.DiGraph, yaml: str):
        step_id = g.nodes[yaml]["id"]
        return cls.id_steps[step_id]

    @classmethod
    def add_flow_events(cls, dependencies: Tuple[set, set, set]):
        """
        Adds the Flow TraceEvents to provide relations between events.

        Args:
            dependencies: Three sets of YAML files
            - initial YAML files (no dependencies)
            - input YAML files (input(s) to a Step),
            - output files (output of a Step).

        """
        g = cls.get_tree_repr(dependencies)
        # Make an undirected copy of the digraph
        ug = g.to_undirected()

        # Every fully disconnected subgraph is a separate Pipe.
        sub_graphs = [g.subgraph(c) for c in nx.connected_components(ug)]
        edge_id = 0
        for pipe_id, sg in enumerate(sub_graphs):
            for edge in sg.edges():
                flow_name = f"pipe_{pipe_id}_flow_{edge_id}"
                start, end = edge
                start_step = cls.get_step_from_yaml(sg, start)
                end_step = cls.get_step_from_yaml(sg, end)
                Tracer.log(TraceEvent(
                    name = flow_name,
                    cat = "hagent",
                    ph = PhaseType.FLOW_START,
                    ts = start_step.ts,
                    pid = HAGENT_PID,
                    tid = start_step.tid,
                    id = edge_id)
                )
                Tracer.log(TraceEvent(
                    name = flow_name,
                    cat = "hagent",
                    ph = PhaseType.FLOW_END,
                    ts = end_step.ts,
                    pid = HAGENT_PID,
                    tid = end_step.tid,
                    id = edge_id,
                    bp="e")
                )
                edge_id += 1

    @classmethod
    def add_metadata(cls, asynchronous: bool):
        """
        Adds metadata events to rename and prettify the Perfetto Trace.
        """
        # Add thread names.
        for step in cls.steps:
            # Handle multi-thread.
            if asynchronous:
                Tracer.log(TraceEvent(
                    name = "thread_name",
                    cat = "__metadata",
                    ph = PhaseType.METADATA,
                    ts = 0,
                    pid = step.pid,
                    tid = step.tid,
                    args = {
                        "name": step.name
                    },
                ))
            else:
                # Default name for non-multi-threaded cases.
                Tracer.log(TraceEvent(
                    name = "thread_name",
                    cat = "__metadata",
                    ph = PhaseType.METADATA,
                    ts = 0,
                    pid = HAGENT_PID,
                    tid = HAGENT_TID,
                    args = {
                        "name": "Pipe"
                    },
                ))
                break
        
        # Add thread names for LLM calls.
        # Necessary to separate this from above for proper placement in Perfetto UI.
        for step in cls.steps:
            if asynchronous:
                if len(step.args["data"]["tracing"]["history"]) > 0:
                    Tracer.log(TraceEvent(
                        name = "thread_name",
                        cat = "__metadata",
                        ph = PhaseType.METADATA,
                        ts = 0,
                        pid = LLM_PID,
                        tid = step.tid,
                        args = {
                            "name": f"{step.name} (LLM_Completions)"
                        },
                    ))
            else:
                # Have one track for LLM Calls
                Tracer.log(TraceEvent(
                    name = "thread_name",
                    cat = "__metadata",
                    ph = PhaseType.METADATA,
                    ts = 0,
                    pid = LLM_PID,
                    tid = LLM_TID,
                    args = {
                        "name": "LLM_Completions"
                    },
                ))
                break

        # Name overarching categories for the PID (Hagent + LLM).
        Tracer.log(TraceEvent(
            name = "process_name",
            cat = "__metadata",
            ph = PhaseType.METADATA,
            ts = 0,
            pid = HAGENT_PID,
            tid = METADATA_TID,
            args = {
                "name":"Hagent"
            },
        ))
        Tracer.log(TraceEvent(
            name = "process_name",
            cat = "__metadata",
            ph = PhaseType.METADATA,
            ts = 0,
            pid = LLM_PID,
            tid = METADATA_TID,
            args = {
                "name": "LiteLLM"
            },
        ))

    @classmethod
    def create_asynchronous_trace(cls, dependencies: Tuple[set, set, set], step_offset: int):
        """
        Creates an asynchronous trace from the recorded events.

        This performs the following algorithm to re-order all events.
        1. Set every Step with no dependence on another Step to timestamp (ts) 0.
            1a. Also set every Step to a new TID to display it on a separate
                track.
        2. Use BFS to move through the dependency tree layer by layer.
            2a. For each layer, set each Step's ts to the latest (ts + dur)
                of its parents.
            2b. For each moved Step, move each non-Step event with the same
                Step ID to match its new ts.

        Args:
            dependencies: Three sets of YAML files
            - initial YAML files (no dependencies)
            - input YAML files (input(s) to a Step),
            - output files (output of a Step).
            step_offset: How far apart to place each layer of Steps from each other in ms.
                         0 indicates that all Steps should be touching if displayed on a single track.

        """
        g = cls.get_tree_repr(dependencies)
        
        visited = set()
        for potential_root in g.nodes:
            # Look for nodes that have no dependencies.
            if len(list(g.predecessors(potential_root))) != 0:
                continue

            # Iterate through Steps via BFS, layer by layer.
            tree_iter = nx.bfs_tree(g, potential_root)
            for layer_idx, layer in enumerate(tree_iter):
                # Ensure the layer is an iterable when 1 element.
                if isinstance(layer, str): layer = [layer]
                for yaml_file in layer:
                    step_id = g.nodes[yaml_file]["id"]
                    step = cls.get_step_from_yaml(g, yaml_file)
                    step.tid = step_id
                    orig_event_ts = step.ts
                    visited.add(yaml_file)
                    # If it is the first layer, we know that steps should be placed at timestamp 0.
                    if layer_idx == 0:
                        step.ts = 0
                    else:
                        # Otherwise, get the last dependency and set that as the last timestamp.
                        dependency_timestamps = []
                        dependency_unvisited = False
                        for dependency in g.pred[yaml_file]:
                            if dependency not in visited:
                                dependency_unvisited = True
                                break
                            step_dependency = cls.get_step_from_yaml(g, dependency)
                            dependency_timestamps.append(step_dependency.ts + step_dependency.dur + step_offset)
                        # If we have an unvisited dependency, that needs to be resolved before we can
                        # apply any timestamp change here. This Step will be revisited since the unvisited dependency
                        # will be visited in the future.
                        if dependency_unvisited is True:
                            continue
                        step.ts = max(dependency_timestamps)
                
                    # Move all related sub-events for this step.
                    for subevent in cls.events:
                        if subevent.cat != "hagent.step" and subevent.args["step_id"] == step_id:
                            interstep_offset = subevent.ts - orig_event_ts
                            step_offset = step.ts
                            subevent.ts = step_offset + interstep_offset
                            subevent.tid = step_id

    @classmethod
    def save_perfetto_trace(cls, dependencies: Tuple[set, set, set],
                            filename: str=None, asynchronous: bool=False, step_offset: int=0):
        """
        Saves the events off in a Perfetto-compatible JSON file.

        Args:
            asynchronous: Dump a trace where all events are not displayed as recorded.
                         The trace will do a best-effort re-ordering to depict
                         a fully asynchronous run.

        """
        if filename is None:
            filename = "hagent.json"
        # Modify the TraceEvents to be fully parallelized.
        if asynchronous:
            cls.create_asynchronous_trace(dependencies, step_offset)
        # Add necessary metadata to visualize each event nicely.
        cls.add_metadata(asynchronous)
        # Add Flow TraceEvents to depict how each step flows into the next.
        cls.add_flow_events(dependencies)

        with open(filename, "w+", encoding="utf-8") as f:
            json.dump({
                "traceEvents": [event.to_json() for event in cls.events]
            }, f, indent=2, default=str)

###############
## METACLASS ##
###############
def trace_function(func):
    """
    Decorator to provide the Tracer logger with all metadata to construct a trace.
    """
    @functools.wraps(func)
    def inner(*args, **kwargs):
        start_time = time.time()
        result = func(*args, **kwargs)
        end_time = time.time()
        # Mark each function as a complete event.
        # We can augment the log with Flow comments later on.
        
        # Ensure all arguments (*args, **kwargs) are JSON serializable.
        serialized_args = []
        serialized_kwargs = {}
        for arg in args:
            serialized_args.append(str(arg))
        for key, val in kwargs.items():
            serialized_kwargs[str(key)] = str(val)

        Tracer.log(TraceEvent(
            # This is C++ syntax, but it is a nice, clean way to show a class::method relationship.
            name = f"{args[0].__class__.__name__}::{func.__name__}",
            cat = "hagent",
            ph = PhaseType.COMPLETE,
            ts = s_to_us(start_time),
            pid = HAGENT_PID,
            tid = threading.get_ident(),
            args = {
                "func": func.__name__,
                "func_args": serialized_args,
                "func_kwargs": serialized_kwargs,
                "func_result": str(result)
            },
            dur = s_to_us(end_time - start_time),
        ))

        return result
    return inner

# https://stackoverflow.com/a/6307917
class TracerMetaClass(type):
    def __new__(cls, name, bases, local):
        """ A MetaClass to append tracing functionality to a class and its subclasses.
        
        Tracing is done via a decorator that will log the following information.
        - Total time for a function taken.
        - Input arguments.
        - Output arguments.

        This allows us to track what functions are dependent on while being minimally invasive to the codebase.
        This also allows us to track overall function time for each function.

        Ensure that all decorators do not obscure decorated function names (i.e. use functools.wraps(func)). This
        allows the appropriate function name to be displayed in the trace.

        You could also do this by generating a cProfile and use another visualizer.

        Example usage that will auto-magically add tracing decorators:
            class BaseClass(metaclass=TracerMetaClass):
                def method_1(self):
                    return 1
                def method_2(self):
                    return 2
        
        Args:
            cls: The class that will be an instance of this TracerMetaClass.
            name: The name of the class.
            bases: The base class of the class.
            local: The attributes of the class as a dictionary.
        
        Returns:
            The constructed class instance.

        """
        for attr in local:
            value = local[attr]

            # Attach the wrapped function in place of any method
            # of the class. This can be further wrapped by any other decorator, but
            # this trace decorator will always be called FIRST out of every decorator.
            # 1. enter this trace_decorator
            # 2.    enter subsequent decorator
            # 3.        run function
            # 4.    exit subsequent decorator
            # 5. exit this trace_decorator
            if callable(value):
                local[attr] = trace_function(value)
        return type.__new__(cls, name, bases, local)

class TracerABCMetaClass(ABCMeta, TracerMetaClass):
    """
    Use this MetaClass when using @abstractmethod/for abstract classes.
    """