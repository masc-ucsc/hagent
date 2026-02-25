#!/usr/bin/env python3
"""
Board Config Sync

Fetches board configuration files from the remote embedskill GitHub repository
and saves them to the local configs/board/ directory.

Can be run standalone: python3 board_sync.py
"""
import os
import sys
import json
import urllib.request
import urllib.error

REMOTE_REPO_API = 'https://api.github.com/repos/masc-ucsc/embedskill/contents/board-integration?ref=dev'


def fetch_remote_board_configs() -> list:
    """
    Fetch board configuration .md files from the remote GitHub repository
    and save them to $HAGENT_ROOT/hagent/mcp/configs/board/.

    Returns:
        List of short-names (filename without .md extension) of all downloaded
        board configs. Returns an empty list if the fetch fails.
    """
    configs_board_path = os.path.join(os.environ.get('HAGENT_ROOT', '.'), 'hagent', 'mcp', 'configs', 'board')
    os.makedirs(configs_board_path, exist_ok=True)

    # Clear existing .md files before writing to avoid stale configs from renames
    for existing in os.listdir(configs_board_path):
        if existing.endswith('.md'):
            os.remove(os.path.join(configs_board_path, existing))

    try:
        req = urllib.request.Request(
            REMOTE_REPO_API,
            headers={'Accept': 'application/vnd.github.v3+json', 'User-Agent': 'hagent-mcp'}
        )
        with urllib.request.urlopen(req) as response:
            files = json.loads(response.read().decode())

        downloaded = []
        for file_info in files:
            if not file_info.get('name', '').endswith('.md'):
                continue
            download_url = file_info.get('download_url')
            if not download_url:
                continue

            filename = file_info['name']
            dest_path = os.path.join(configs_board_path, filename)

            with urllib.request.urlopen(download_url) as r:
                content = r.read()
            with open(dest_path, 'wb') as f:
                f.write(content)
            downloaded.append(filename.replace('.md', ''))

        return downloaded

    except urllib.error.URLError as e:
        print(f"Warning: Failed to fetch remote board configs: {e}", file=sys.stderr)
        return []
    except Exception as e:
        print(f"Warning: Unexpected error fetching board configs: {e}", file=sys.stderr)
        return []


if __name__ == '__main__':
    boards = fetch_remote_board_configs()
    if boards:
        print(f"Downloaded {len(boards)} board config(s):")
        for b in boards:
            print(f"  - {b}")
    else:
        print("No board configs downloaded. Check HAGENT_ROOT and network connectivity.", file=sys.stderr)
        sys.exit(1)
