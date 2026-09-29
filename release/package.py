#!/usr/bin/env python3
"""Package the committed research artifact without publishing it."""
from datetime import datetime, timezone
import gzip
import hashlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[1]
VERSION = '1.1.0'
NAME = f'bfs-avoidance-frontier-v{VERSION}'


def git(*args):
    return subprocess.check_output(['git', '-C', str(ROOT), *args])


def main():
    subprocess.run(['python3', str(ROOT / 'release/verify.py')], check=True)
    assert not git('diff', '--name-only'), 'Commit tracked changes before packaging'
    assert not git('diff', '--cached', '--name-only'), 'Commit the index before packaging'
    commit = git('rev-parse', 'HEAD').decode().strip()
    timestamp = int(git('show', '-s', '--format=%ct', 'HEAD'))
    names = [n for n in git('ls-files', '-z').decode().split('\0') if n]
    assert not any('.DS_Store' in n or n.startswith('release/dist/') for n in names)
    dist = ROOT / 'release/dist'
    dist.mkdir(exist_ok=True)
    archive = dist / f'{NAME}.tar.gz'
    members = []
    with archive.open('wb') as output:
        with gzip.GzipFile(fileobj=output, mode='wb', filename='', mtime=timestamp) as compressed:
            with tarfile.open(fileobj=compressed, mode='w') as tar:
                for name in sorted(names):
                    payload = git('show', f'{commit}:{name}')
                    mode = git('ls-files', '-s', '--', name).decode().split()[0]
                    info = tarfile.TarInfo(f'{NAME}/{name}')
                    info.size = len(payload)
                    info.mtime = timestamp
                    info.mode = 0o755 if mode == '100755' else 0o644
                    info.uid = info.gid = 0
                    info.uname = info.gname = ''
                    tar.addfile(info, io.BytesIO(payload))
                    members.append({'path': name, 'bytes': len(payload),
                                    'sha256': hashlib.sha256(payload).hexdigest()})
    pdf = dist / f'{NAME}.pdf'
    shutil.copyfile(ROOT / 'paper/main.pdf', pdf)
    assets = {p.name: {'bytes': p.stat().st_size, 'sha256': hashlib.sha256(p.read_bytes()).hexdigest()}
              for p in (archive, pdf)}
    manifest = {'schema_version': 1, 'version': VERSION, 'source_commit': commit,
                'repository': 'https://github.com/vicotrbb/bfs-avoidance-frontier',
                'created_at_utc': datetime.now(timezone.utc).isoformat(),
                'archive_root': NAME, 'member_count': len(members),
                'members': members, 'assets': assets,
                'scope': 'All committed research sources, paper, data, b-files, certificates, scripts, and validation receipts.',
                'licenses': {'code': 'MIT', 'manuscript_documentation_original_data': 'CC-BY-4.0'}}
    (dist / 'RELEASE.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps({'source_commit': commit, 'members': len(members), 'assets': assets}, indent=2))


if __name__ == '__main__':
    main()
