#!/usr/bin/env python3
"""Verify every member of the release archive before optional extraction."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import tarfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('manifest', type=Path)
    parser.add_argument('archive', type=Path)
    parser.add_argument('--extract', type=Path)
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    expected_asset = manifest['assets'][args.archive.name]
    assert args.archive.stat().st_size == expected_asset['bytes']
    assert hashlib.sha256(args.archive.read_bytes()).hexdigest() == expected_asset['sha256']
    root = manifest['archive_root']
    expected = {f"{root}/{item['path']}": item for item in manifest['members']}
    assert len(expected) == manifest['member_count']
    with tarfile.open(args.archive, 'r:gz') as tar:
        members = tar.getmembers()
        assert len(members) == len(expected)
        assert {m.name for m in members} == set(expected)
        for member in members:
            path = PurePosixPath(member.name)
            assert member.isfile() and not path.is_absolute() and '..' not in path.parts
            content = tar.extractfile(member).read()
            item = expected[member.name]
            assert len(content) == item['bytes']
            assert hashlib.sha256(content).hexdigest() == item['sha256'], member.name
        if args.extract:
            args.extract.mkdir(parents=True, exist_ok=True)
            for member in members:
                destination = args.extract / member.name
                assert not destination.exists(), f'Refusing to overwrite {destination}'
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(tar.extractfile(member).read())
                destination.chmod(member.mode)
    print(json.dumps({'status': 'pass', 'source_commit': manifest['source_commit'],
                      'members_verified': len(expected), 'archive_sha256': expected_asset['sha256']}, indent=2))


if __name__ == '__main__':
    main()
