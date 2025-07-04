"""
Script to build a Perfetto Trace from a run directory with input/output YAML files.
"""

import argparse
import logging

from pathlib import Path

from typing import (
    List,
)

from hagent.core.tracer import (
    Tracer,
    parse_yaml_files,
    scan_for_yamls,
)

LOG_FILE = 'perfetto_trace.log'

logger = logging.getLogger(__name__)


def parse_arguments() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description='Perfetto trace builder using a directory of Step input/outputs.')
    parser.add_argument(
        '-i',
        '--input-dir',
        type=str,
        default='.',
        help='Scans this directory for YAML files generated by Steps.'
    )
    parser.add_argument(
        '--asynchronous',
        action='store_true',
        help='Builds a Perfetto trace that displays Steps as parallel as possible.'
    )
    parser.add_argument(
        '-o',
        '--output-file',
        type=str,
        default='perfetto.json',
        help='Name of the output Perfetto Trace.')
    parser.add_argument(
        '--step-offset',
        type=int,
        default=0,
        help='How far apart Steps should be placed in an asynchronous trace.'
    )
    parser.add_argument(
        '--log-level',
        type=str,
        default="INFO",
        choices=["DEBUG", "INFO", "WARNING", "ERROR", "CRITICAL"],
        help=f'Logging level that is stored in {LOG_FILE}. Default is INFO')
    return parser


def generate_perfetto_trace(input_dir: Path, yaml_files: List[Path], output_file: str, asynchronous: bool, step_offset: int):
    """
    Generates a Perfetto Trace given all relevant YAML files.

    Args:
        input_dir: The directory path with all YAML files.
        yaml_files: The list of relevant YAML files to include in the trace.
        output_file: The output file to dump the Perfetto Trace to.
        asynchronous: Disregard the actual execution and display an asynchronous ordering.
        step_offset: How far apart Steps should be spaced in the Perfetto timeline.

    """
    # Initial YAMLs used as inputs for a Pipe.
    initial, inputs, outputs = parse_yaml_files(input_dir, yaml_files)

    logger.debug('Initial YAML files: %s', initial)
    logger.debug('Input YAML files: %s', inputs)
    logger.debug('Output YAML files: %s', outputs)

    Tracer.save_perfetto_trace(
        dependencies=(initial, inputs, outputs), filename=output_file, asynchronous=asynchronous, step_offset=step_offset
    )


def main():
    parser = parse_arguments()
    args = parser.parse_args()

    logging.basicConfig(filename=LOG_FILE, level=args.log_level)
    # Print to STDOUT as well in DEBUG mode.
    if logging.getLevelName(args.log_level) <= logging.DEBUG:
        stream_handler = logging.StreamHandler()
        stream_handler.setLevel(args.log_level)
        logging.getLogger().addHandler(stream_handler)

    yaml_files = scan_for_yamls(args.input_dir)
    logger.info('Gathered YAML files: %s' % yaml_files)
    generate_perfetto_trace(Path(args.input_dir), yaml_files, args.output_file, args.asynchronous, args.step_offset)
    logger.info('Finished generated Perfetto trace: [%s]', args.output_file)


if __name__ == '__main__':
    main()
