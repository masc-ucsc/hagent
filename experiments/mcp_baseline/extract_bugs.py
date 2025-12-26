import yaml
import sys

input_file = sys.argv[1]
output_dir = sys.argv[2]

with open(input_file) as f:
    data = yaml.safe_load(f)

for i, bug in enumerate(data['bugs'], 1):
    filename = f'{output_dir}/bug_{i:02d}_{bug["file"].replace(".sv", "")}.diff'
    with open(filename, 'w') as out:
        out.write(bug['unified_diff'])
    print(f'Created {filename}')
