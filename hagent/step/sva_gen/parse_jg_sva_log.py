# Analyze the formal verified jasper gold assertion file and categorized into two kinds: useful, failed. Write the result into a csv file.

import re
import csv


def parse_jg_sva_log(file_path):
    results = []
    seen_properties = set()
    proven_property_count = 0
    failed_property_count = 0

    # Define regex patterns for extracting information
    proven_pattern = re.compile(r'The property "(?P<property>[\w\.]+)" was proven')
    failed_pattern = re.compile(r'A counterexample \(cex\) .*? for the property "(?P<property>[\w\.]+)"')
    proven_count_pattern = re.compile(r'- proven\s+:\s(?P<count>(\d+))')
    failed_count_pattern = re.compile(r'- cex\s+:\s(?P<count>(\d+))')

    # Read the log file and parse each line
    with open(file_path, 'r') as file:
        for line in file:
            if 'was proven' in line:
                match = proven_pattern.search(line)
                if match:
                    property_name = match.group('property')
                    if property_name not in seen_properties:
                        seen_properties.add(property_name)
                        results.append({'property': property_name, 'result': 'useful'})
            elif 'A counterexample (cex)' in line:
                match = failed_pattern.search(line)
                if match:
                    property_name = match.group('property')
                    if property_name not in seen_properties:
                        seen_properties.add(property_name)
                        results.append({'property': property_name, 'result': 'failed'})
            if '- proven' in line:
                match = proven_count_pattern.search(line)
                if match:
                    proven_property_count = int(match.group('count'))
            if '- cex' in line:
                match = failed_count_pattern.search(line)
                if match:
                    failed_property_count = int(match.group('count'))

    return results, proven_property_count, failed_property_count


def summarize_results(results, proven_count, failed_count):
    total = len(results)
    useful_count = sum(1 for result in results if result['result'] == 'useful')
    failed_count_actual = sum(1 for result in results if result['result'] == 'failed')

    if useful_count == proven_count and failed_count_actual == failed_count:
        print('Successfully extracted the Jg log file for useful and failed assertions!')
    else:
        if useful_count != proven_count:
            print(f'Warning: Proven count mismatch. Expected {proven_count}, found {useful_count}.')
        if failed_count_actual != failed_count:
            print(f'Warning: Failed count mismatch. Expected {failed_count}, found {failed_count_actual}.')

    return total, useful_count, failed_count_actual


def save_results_to_csv(results, output_file):
    try:
        with open(output_file, 'w', newline='') as csvfile:
            csvwriter = csv.writer(csvfile)
            csvwriter.writerow(['Result', 'Property'])
            for result in results:
                csvwriter.writerow([result['result'], result['property']])
        csvfile.close()
    except Exception as e:
        print(f'Error saving results to CSV: {e}')


# extract the sva and comments by LLM to write to the .csv file
def extract_assertions(file_path, jg_log_results, output_csv):
    results = []

    # Define regex patterns for comments
    comment_pattern = re.compile(r'//\s*(?P<comment>.+)')

    with open(file_path, 'r') as file:
        lines = file.readlines()

    for log_result in jg_log_results:
        property_name = log_result['property'].split('.')[-1]  # Get the last part of the property name
        content = ''
        comments = []

        for i, line in enumerate(lines):
            if property_name in line:
                # Extract related comments above the property
                for j in range(i - 1, -1, -1):
                    comment_match = comment_pattern.search(lines[j])
                    if comment_match:
                        comments.insert(0, comment_match.group('comment'))
                    else:
                        break

                # Extract the SVA content
                content = line.strip()
                break

        results.append(
            {
                'property': log_result['property'],
                'result': log_result['result'],
                'content': content,
                'comments': ' '.join(comments),
            }
        )

    # Save to CSV
    with open(output_csv, 'w', newline='') as csvfile:
        csvwriter = csv.writer(csvfile)
        csvwriter.writerow(['Result', 'Property', 'Content', 'Comments'])
        for result in results:
            csvwriter.writerow([result['result'], result['property'], result['content'], result['comments']])


# Example file path
jg_log_path = '/soe/czeng14/projects/AutoSVA/projs/mmu/sessionLogs/session_0/jg_session_0.log'
sva_csv_file_path = '/soe/czeng14/projects/SVA/mmu_sva_jg.csv'
assertion_file_path = '/soe/czeng14/projects/SVA/mmu/sva/mmu_prop.sv.2.save'


def jg_post_process(jg_log_path, sva_csv_file_path, assertion_file_path):
    # Parse the log and print results
    parsed_results, proven_count, failed_count = parse_jg_sva_log(jg_log_path)
    total_properties, useful_properties, failed_properties = summarize_results(parsed_results, proven_count, failed_count)

    save_results_to_csv(parsed_results, sva_csv_file_path)

    # Extract assertions and align with log results
    extract_assertions(assertion_file_path, parsed_results, sva_csv_file_path)

    # Print the summary
    print(f'Total properties run: {total_properties}')
    print(f'Useful properties: {useful_properties}')
    print(f'Failed properties: {failed_properties}')
