#!/usr/bin/env python3
"""
Config Sync

Fetches board and platform configuration files from the remote embedskill
GitHub repository and saves them to the local configs/ directory.

Clears the entire configs/ directory on each run to prevent stale files.

Can be run standalone: python3 config_sync.py
"""

import os
import sys
import json
import shutil
import urllib.request
import urllib.error

REMOTE_REPO_DATA_API = 'https://api.github.com/repos/masc-ucsc/embedskill/contents/data?ref=dev/board-integration'


def fetch_remote_configs() -> dict:
    """
    Fetch board and platform configuration .md files from the remote GitHub
    repository and save them to $HAGENT_ROOT/hagent/mcp/configs/.

    Clears the entire configs/ directory before writing to ensure no stale
    or renamed files remain.

    Returns:
        Dict with keys matching remote subdirectory names (e.g. 'board',
        'platform'), each containing a list of short-names (filename without
        .md extension) of downloaded configs.
        Returns {'board': [], 'platform': []} on failure.
    """
    hagent_root = os.environ.get('HAGENT_ROOT')
    if not hagent_root:
        print('Error: HAGENT_ROOT environment variable is not set.', file=sys.stderr)
        return {'board': [], 'platform': []}

    configs_path = os.path.join(hagent_root, 'hagent', 'mcp', 'configs')

    # Clear the entire configs directory before re-populating
    if os.path.isdir(configs_path):
        for item in os.listdir(configs_path):
            item_path = os.path.join(configs_path, item)
            if os.path.isdir(item_path):
                shutil.rmtree(item_path)
            else:
                os.remove(item_path)

    os.makedirs(configs_path, exist_ok=True)
    result = {}

    try:
        # Fetch the top-level data/ directory listing
        req = urllib.request.Request(
            REMOTE_REPO_DATA_API, headers={'Accept': 'application/vnd.github.v3+json', 'User-Agent': 'hagent-mcp'}
        )
        with urllib.request.urlopen(req) as response:
            entries = json.loads(response.read().decode())

        for entry in entries:
            if entry.get('type') != 'dir':
                continue

            subdir_name = entry['name']  # e.g. 'board' or 'platform'
            subdir_url = entry['url']
            local_subdir = os.path.join(configs_path, subdir_name)
            os.makedirs(local_subdir, exist_ok=True)

            # Fetch the file listing for this subdirectory
            sub_req = urllib.request.Request(
                subdir_url, headers={'Accept': 'application/vnd.github.v3+json', 'User-Agent': 'hagent-mcp'}
            )
            with urllib.request.urlopen(sub_req) as sub_response:
                files = json.loads(sub_response.read().decode())

            downloaded = []
            for file_info in files:
                if not file_info.get('name', '').endswith('.md'):
                    continue
                download_url = file_info.get('download_url')
                if not download_url:
                    continue

                filename = file_info['name']
                dest_path = os.path.join(local_subdir, filename)

                with urllib.request.urlopen(download_url) as r:
                    content = r.read()
                with open(dest_path, 'wb') as f:
                    f.write(content)
                downloaded.append(filename.replace('.md', ''))

            result[subdir_name] = downloaded

        return result

    except urllib.error.URLError as e:
        print(f'Warning: Failed to fetch remote configs: {e}', file=sys.stderr)
        return {'board': [], 'platform': []}
    except Exception as e:
        print(f'Warning: Unexpected error fetching remote configs: {e}', file=sys.stderr)
        return {'board': [], 'platform': []}


if __name__ == '__main__':
    result = fetch_remote_configs()
    total = sum(len(v) for v in result.values())
    if total:
        print(f'Downloaded {total} config file(s):')
        for subdir, names in result.items():
            for name in names:
                print(f'  [{subdir}] {name}')
    else:
        print('No configs downloaded. Check HAGENT_ROOT and network connectivity.', file=sys.stderr)
        sys.exit(1)
