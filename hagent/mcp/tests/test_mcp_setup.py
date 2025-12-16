"""
Integration test for MCP setup with the simplechisel template.

Flow:
1. Create an isolated temp directory.
2. Run scripts/setup_mcp.sh simplechisel to generate repo/build/cache/logs and hagent_server.sh.
3. Register the MCP with `claude mcp add hagent ./hagent_server.sh` or `gemini mcp add hagent ./hagent_server.sh` and confirm it shows as Connected.
"""

import os
import subprocess
import unittest
import uuid
from pathlib import Path


class TestMCPSetupIntegration(unittest.TestCase):
    """End-to-end checks for MCP setup with Claude and/or Gemini."""

    CLIENTS = ('claude', 'gemini')

    @classmethod
    def setUpClass(cls):
        cls.hagent_root = Path(__file__).resolve().parents[3]
        cls.setup_script = cls.hagent_root / 'scripts' / 'setup_mcp.sh'

        cls.available_clients = []
        for client in cls.CLIENTS:
            try:
                result = subprocess.run([client, '--version'], capture_output=True, text=True, timeout=10)
                if result.returncode != 0:
                    continue
                list_result = subprocess.run([client, 'mcp', 'list'], capture_output=True, text=True, timeout=15)
                if list_result.returncode == 0:
                    cls.available_clients.append(client)
            except (subprocess.CalledProcessError, FileNotFoundError, subprocess.TimeoutExpired):
                continue

        if not cls.available_clients:
            raise unittest.SkipTest('No MCP-capable CLI (claude/gemini) is installed or accessible')

        if not cls.setup_script.exists():
            raise unittest.SkipTest('scripts/setup_mcp.sh not found')

    def setUp(self):
        self.base_dir = self.hagent_root / 'output' / 'test_mcp_setup'
        self.base_dir.mkdir(parents=True, exist_ok=True)
        self.test_dir = self.base_dir / f'{self._testMethodName}_{uuid.uuid4().hex[:8]}'
        self.test_dir.mkdir(parents=True, exist_ok=False)
        self.hagent_server = self.test_dir / 'hagent_server.sh'

        env = {**os.environ, 'HAGENT_ROOT': str(self.hagent_root)}
        setup_result = subprocess.run(
            [str(self.setup_script), 'simplechisel'],
            capture_output=True,
            text=True,
            timeout=600,
            cwd=self.test_dir,
            env=env,
        )

        if setup_result.returncode != 0:
            self.fail(f'setup_mcp.sh failed: {setup_result.stderr}')

        if not self.hagent_server.exists():
            self.fail('Expected hagent_server.sh to be created by setup_mcp.sh')

        self.hagent_server.chmod(self.hagent_server.stat().st_mode | 0o111)

        for client in self.available_clients:
            self._remove_hagent_mcp(client)
            self._add_hagent_mcp(client)

    def tearDown(self):
        for client in self.available_clients:
            self._remove_hagent_mcp(client)

    def _remove_hagent_mcp(self, client: str):
        """Ensure a clean MCP entry for hagent on the given client."""
        try:
            subprocess.run(
                [client, 'mcp', 'remove', 'hagent'],
                capture_output=True,
                text=True,
                timeout=30,
            )
        except subprocess.TimeoutExpired:
            pass

    def _add_hagent_mcp(self, client: str):
        """Register hagent_server.sh with the given client."""
        add_result = subprocess.run(
            [client, 'mcp', 'add', 'hagent', './hagent_server.sh'],
            capture_output=True,
            text=True,
            timeout=120,
            cwd=self.test_dir,
        )

        if add_result.returncode != 0:
            self.fail(f'Failed to add hagent MCP with {client}: {add_result.stderr or add_result.stdout}')

    def _assert_mcp_connected(self):
        """Check that hagent shows up as a connected MCP server for all available clients."""
        outputs = {}
        for client in self.available_clients:
            list_result = subprocess.run(
                [client, 'mcp', 'list'],
                capture_output=True,
                text=True,
                timeout=60,
                cwd=self.test_dir,
            )

            if list_result.returncode != 0:
                self.fail(f'{client} mcp list failed: {list_result.stderr}')

            output = list_result.stdout
            outputs[client] = output
            self.assertIn('hagent:', output, f'hagent MCP entry missing from {client} mcp list output')
            self.assertIn('Connected', output, f'hagent MCP is not reported as Connected for {client}')

        return outputs

    def test_mcp_setup_and_list(self):
        """Validate setup_mcp.sh output and MCP registration for available clients."""
        outputs = self._assert_mcp_connected()
        for client, output in outputs.items():
            self.assertIn('hagent_server.sh', output, f'{client} did not record the expected server script path')


if __name__ == '__main__':
    unittest.main(verbosity=2, failfast=True)
