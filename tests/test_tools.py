#!/usr/bin/env python3
"""Regression checks for the standalone tools; run with python3 test_tools.py."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest


TOOLS = Path(__file__).resolve().parent.parent / 'tools'


class ToolTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='bend tools test ')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.bin = self.root / 'bin'
        self.bin.mkdir()
        self.env = dict(os.environ, PATH=f'{self.bin}:{os.environ["PATH"]}')
        self.env['XDG_CACHE_HOME'] = str(self.root / 'cache')
        self.write('bin/curl', '#!/bin/sh\nprintf \'{"tag_name": "v2.0.36"}\\n\'\n',
                   executable=True)
        self.write('bin/bend', '#!/bin/sh\necho "bend 2.0.36"\n', executable=True)

    def write(self, name, content, executable=False):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
        if executable:
            path.chmod(0o755)
        return path

    def git(self, *args):
        return subprocess.run(['git', *args], cwd=self.root, check=True,
                              capture_output=True, text=True)

    def repo(self):
        self.git('init', '-q', '-b', 'main')

    def run_tool(self, name, *args):
        return subprocess.run([str(TOOLS / name), *map(str, args)], cwd=self.root,
                              env=self.env, capture_output=True, text=True)

    def test_charsplit_rejects_invalid_codes(self):
        for codes in [(), ('-1',), ('4294967296',), ('65', '65')]:
            with self.subTest(codes=codes):
                got = self.run_tool('charsplit.py', 'OTHER', *codes)
                self.assertEqual(got.returncode, 2)
                self.assertIn('error:', got.stderr)
        got = self.run_tool('charsplit.py', 'OTHER', '65', '66')
        self.assertEqual(got.returncode, 0)
        self.assertIn('Inl{{==}}', got.stdout)

    def test_version_pin_warns_for_new_release_without_blocking(self):
        self.write('bin/curl', '''#!/bin/sh
mkdir -p "$XDG_CACHE_HOME"
echo called >> "$XDG_CACHE_HOME/curl_calls"
printf '{"tag_name": "v2.0.37"}\\n'
''', executable=True)
        for _ in range(2):
            got = self.run_tool('charsplit.py', 'OTHER', '65')
            self.assertEqual(got.returncode, 0, got.stderr)
            self.assertIn('pinned to Bend 2.0.36; latest release is 2.0.37', got.stderr)
        calls = (self.root / 'cache/curl_calls').read_text().splitlines()
        self.assertEqual(calls, ['called'])

    def test_version_pin_warns_for_installed_mismatch(self):
        self.write('bin/bend', '#!/bin/sh\necho "bend 2.0.35"\n', executable=True)
        got = self.run_tool('charsplit.py', 'OTHER', '65')
        self.assertEqual(got.returncode, 0, got.stderr)
        self.assertIn('pinned to Bend 2.0.36; installed Bend is 2.0.35', got.stderr)

    def test_version_lookup_failure_warns_without_blocking(self):
        self.write('bin/curl', '#!/bin/sh\nexit 22\n', executable=True)
        got = self.run_tool('charsplit.py', 'OTHER', '65')
        self.assertEqual(got.returncode, 0, got.stderr)
        self.assertIn('could not verify latest Bend release', got.stderr)

    def test_every_utility_runs_version_advisory(self):
        self.repo()
        self.write('bin/curl', '#!/bin/sh\nprintf \'{"tag_name": "v2.0.37"}\\n\'\n',
                   executable=True)
        for name in ('bench.sh', 'chk.sh', 'kernel.sh', 'lawcheck.sh',
                     'perlaw.sh', 'rc.sh', 'charsplit.py'):
            with self.subTest(name=name):
                got = self.run_tool(name)
                self.assertIn('latest release is 2.0.37', got.stderr)

    def test_chk_only_hides_exact_allowlisted_defs(self):
        self.repo()
        self.write('run.bend', 'def known:\n  0n\n')
        self.write('bin/bend', '''#!/bin/sh
cat <<'EOF'
SOME PROOFS FAIL
Error: 2 defs rely on unsafe or foreign code:
- known
- newly_added
Use --verdict for mathematical validity.
EOF
exit 1
''', executable=True)
        self.write('expected.tsv', 'run.bend\tknown\n')
        got = self.run_tool('chk.sh', '-e', 'expected.tsv', 'run.bend')
        self.assertEqual(got.returncode, 1)
        self.assertIn('newly_added: relies', got.stdout)
        self.write('expected.tsv', 'run.bend\tknown\nrun.bend\tnewly_added\n')
        got = self.run_tool('chk.sh', '-e', 'expected.tsv', 'run.bend')
        self.assertEqual(got.returncode, 0, got.stdout + got.stderr)
        self.assertIn('1 ok, 0 with errors', got.stdout)

    def test_chk_project_allowlist_exposes_new_unsafe_def(self):
        self.repo()
        self.write('run.bend', 'def known:\n  0n\n')
        self.write('bin/bend', '''#!/bin/sh
if [ "$1" = version ]; then echo 'bend 2.0.36'; exit 0; fi
cat <<'EOF'
SOME PROOFS FAIL
Error: 2 defs rely on unsafe or foreign code:
- Sys.isatty
- newly_added
EOF
exit 1
''', executable=True)
        got = self.run_tool('chk.sh', 'run.bend')
        self.assertEqual(got.returncode, 1)
        self.assertIn('newly_added: relies', got.stdout)
        self.assertNotIn('Sys.isatty: relies', got.stdout)

    def test_perlaw_keeps_qualified_names_distinct_and_handles_spaces(self):
        self.repo()
        self.write('A.bend', 'law foo:\n  {0n == 0n}\n')
        self.write('B.bend', 'law foo:\n  {0n == 0n}\n')
        self.write('proof dir/PROOF.bend', '''import ../A.bend as A
import ../B.bend as B
def A.foo:
  {==}
def B.foo:
  {==}
''')
        self.write('bin/bend', '''#!/bin/sh
n=2
grep -q '^def A.foo' "$1" && n=$((n - 1))
grep -q '^def B.foo' "$1" && n=$((n - 1))
if [ "$n" = 0 ]; then echo 'ALL PROOFS CHECK'; exit 0; fi
echo "Error: $n TODOs found."
exit 1
''', executable=True)
        self.write('tmp/perlaw/sentinel', 'keep')
        got = self.run_tool('perlaw.sh', 'proof dir/PROOF.bend')
        self.assertEqual(got.returncode, 0, got.stdout + got.stderr)
        self.assertIn('ok      A.foo', got.stdout)
        self.assertIn('ok      B.foo', got.stdout)
        self.assertEqual((self.root / 'tmp/perlaw/sentinel').read_text(), 'keep')

    def test_lawcheck_preserves_other_scratch(self):
        self.repo()
        self.write('cli.bend', 'def value:\n  0n\n')
        self.write('LAWS.bend', 'law first:\n  ?TODO\n')
        self.git('add', 'cli.bend', 'LAWS.bend')
        self.git('-c', 'user.name=Test', '-c', 'user.email=test@example.com',
                 'commit', '-qm', 'base')
        self.write('LAWS.bend', 'law first:\n  ?TODO\nlaw second:\n  ?TODO\n')
        self.write('tmp/lawcheck/sentinel', 'keep')
        self.write('bin/bend', '''#!/bin/sh
n=$(grep -c '^law ' "$1" || true)
if [ "$n" = 0 ]; then echo 'ALL PROOFS CHECK'; exit 0; fi
echo "Error: $n TODOs found."
exit 1
''', executable=True)
        got = self.run_tool('lawcheck.sh')
        self.assertEqual(got.returncode, 0, got.stdout + got.stderr)
        self.assertIn('+1 TODOs = 1 new laws: second', got.stdout)
        self.assertEqual((self.root / 'tmp/lawcheck/sentinel').read_text(), 'keep')

    def test_kernel_preserves_other_scratch(self):
        self.repo()
        self.write('PROOF.bend', 'law foo:\n  {0n == 0n}\n')
        self.write('tmp/kernel/PROOF.bendtt', 'keep')
        self.write('bin/bend', '''#!/bin/sh
if [ "$2" = -o ]; then printf 'proof' >"$3"; fi
''', executable=True)
        kernel = self.write('bin/bendtt', '#!/bin/sh\necho "ALL PROOFS CHECK"\n',
                            executable=True)
        self.env['BENDTT'] = str(kernel)
        got = self.run_tool('kernel.sh')
        self.assertEqual(got.returncode, 0, got.stdout + got.stderr)
        self.assertEqual((self.root / 'tmp/kernel/PROOF.bendtt').read_text(), 'keep')

    def test_rc_keeps_cli_run_scope(self):
        source = self.write('app.c', '''// Spins
// =====
// Segments
// =====
case WL_CASE(FID_CLI_FOO):
  term_keep(x);
case WL_CASE(FID_RUN_BAR):
  ctr_take(x);
case WL_CASE(FID_OTHER_BAZ):
  rfc_seal(x);
''')
        got = self.run_tool('rc.sh', source)
        self.assertEqual(got.returncode, 0, got.stdout + got.stderr)
        self.assertIn('FID_CLI_FOO 1 0 0', got.stdout)
        self.assertIn('FID_RUN_BAR 0 1 0', got.stdout)
        self.assertNotIn('FID_OTHER_BAZ', got.stdout)

    def test_bench_rejects_failed_run_and_keeps_other_scratch(self):
        self.repo()
        self.write('app.bend', 'old\n')
        self.git('add', 'app.bend')
        self.git('-c', 'user.name=Test', '-c', 'user.email=test@example.com',
                 'commit', '-qm', 'base')
        self.write('app.bend', 'new\n')
        self.write('tmp/bench/sentinel', 'keep')
        self.write('bin/sysctl', '#!/bin/sh\necho 2\n', executable=True)
        self.write('bin/bend', '''#!/bin/sh
while [ "$#" -gt 0 ]; do
  if [ "$1" = -o ]; then
    shift
    printf '#!/bin/sh\\necho app failed >&2\\nexit 7\\n' >"$1"
    chmod +x "$1"
    exit 0
  fi
  shift
done
exit 2
''', executable=True)
        got = self.run_tool('bench.sh', '-L', '999999', '-n', '1', 'app.bend')
        self.assertEqual(got.returncode, 1, got.stdout + got.stderr)
        self.assertRegex(got.stderr, r'old\.1\.warm exited [17]')
        self.assertIn('app failed', got.stderr)
        self.assertNotIn('peak RSS', got.stdout)
        self.assertEqual((self.root / 'tmp/bench/sentinel').read_text(), 'keep')


if __name__ == '__main__':
    unittest.main()
