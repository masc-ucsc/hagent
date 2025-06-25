#!/usr/bin/env python3
import json
import argparse
import sys


def list_fields(input_file):
    """List all available fields in the JSON file."""
    data = load_json_data(input_file)

    print(f"JSON structure analysis for '{input_file}':")
    print(f'Number of entries: {len(data)}')

    # Collect all unique fields across all entries
    all_fields = set()
    field_types = {}
    field_counts = {}

    for i, entry in enumerate(data):
        if isinstance(entry, dict):
            for field in entry.keys():
                all_fields.add(field)
                field_counts[field] = field_counts.get(field, 0) + 1

                # Track field types
                if field not in field_types:
                    field_types[field] = type(entry[field]).__name__
        else:
            print(f'Warning: Entry {i + 1} is not a dictionary')

    print('\nAvailable fields:')
    for field in sorted(all_fields):
        count = field_counts[field]
        ftype = field_types[field]
        print(f'  {field:<20} (appears in {count}/{len(data)} entries, type: {ftype})')

    print(f'\nTo extract a field, use: python {sys.argv[0]} {input_file} -f FIELD_NAME')


def load_json_data(input_file):
    """Load JSON data, handling both regular JSON and JSON Lines formats."""
    try:
        with open(input_file, 'r', encoding='utf-8') as f:
            # Try to load as regular JSON first
            try:
                f.seek(0)
                return json.load(f)
            except json.JSONDecodeError:
                # If that fails, try JSON Lines format
                f.seek(0)
                data = []
                for line_num, line in enumerate(f, 1):
                    line = line.strip()
                    if line:  # Skip empty lines
                        try:
                            data.append(json.loads(line))
                        except json.JSONDecodeError as e:
                            print(f'Error parsing line {line_num}: {e}', file=sys.stderr)
                            continue
                return data
    except FileNotFoundError:
        print(f"Error: Input file '{input_file}' not found.", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error reading '{input_file}': {e}", file=sys.stderr)
        sys.exit(1)


def extract_data(input_file, field_name='prompt', output_file=None):
    """Extract specified field from JSON file and write to output file or stdout."""
    data = load_json_data(input_file)

    # Determine output destination
    if output_file:
        try:
            output = open(output_file, 'w', encoding='utf-8')
        except Exception as e:
            print(f"Error opening output file '{output_file}': {e}", file=sys.stderr)
            sys.exit(1)
    else:
        output = sys.stdout

    try:
        for i, entry in enumerate(data):
            if isinstance(entry, dict):
                field_value = entry.get(field_name, '')

                # Handle different data types
                if isinstance(field_value, (list, dict)):
                    field_content = json.dumps(field_value, indent=2)
                else:
                    field_content = str(field_value).strip()

                # Debug output to help diagnose issues
                if not field_content and field_name in entry:
                    print(f"Warning: Field '{field_name}' exists in entry {i + 1} but appears empty", file=sys.stderr)
                elif field_name not in entry:
                    print(f"Warning: Field '{field_name}' not found in entry {i + 1}", file=sys.stderr)
                    continue
            else:
                print(f'Warning: Entry {i + 1} is not a dictionary, skipping.', file=sys.stderr)
                continue

            if field_content:
                output.write(f'### {field_name.title()} {i + 1} ###\n')
                output.write(field_content + '\n\n')
            elif field_name in entry:
                # Handle the case where field exists but is empty/None
                output.write(f'### {field_name.title()} {i + 1} (Empty) ###\n')
                output.write('[Empty or None value]\n\n')
    finally:
        # Close file if we opened one
        if output_file and output != sys.stdout:
            output.close()


def main():
    parser = argparse.ArgumentParser(
        description='Extract specified field from JSON or JSON Lines file entries and output to stdout or file.'
    )
    parser.add_argument('input_file', help='Input JSON or JSON Lines (.jsonl) file containing data entries')
    parser.add_argument(
        '-f', '--field', dest='field_name', default='prompt', help='Field name to extract from each entry (default: prompt)'
    )
    parser.add_argument('-o', '--output', dest='output_file', help='Output file (default: stdout)')
    parser.add_argument('--list-fields', action='store_true', help='List all available fields in the JSON and exit')

    args = parser.parse_args()

    # If --list-fields is specified, show available fields and exit
    if args.list_fields:
        list_fields(args.input_file)
        return

    extract_data(args.input_file, args.field_name, args.output_file)


if __name__ == '__main__':
    main()
