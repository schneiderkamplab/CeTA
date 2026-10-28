#!/usr/bin/env python3
"""Check the repository's OKF 0.2 profile (requires PyYAML).

This checks documentation structure, never runtime architecture or soundness.
"""
import argparse
import datetime
from pathlib import Path
import re
import sys
import yaml


def frontmatter(text):
    if not text.startswith('---\n'):
        return None
    parts = text.split('\n---\n', 1)
    if len(parts) != 2:
        raise ValueError('unterminated frontmatter')
    value = yaml.safe_load(parts[0][4:])
    if not isinstance(value, dict):
        raise ValueError('frontmatter must be a mapping')
    return value


def check(root):
    root = Path(root)
    errors = []
    if not root.is_dir():
        return [f'{root}: missing bundle']
    paths = sorted(root.rglob('*.md'))
    directories = {root}
    for path in paths:
        directories.add(path.parent)
        directories.update(p for p in path.parent.parents if root in p.parents)
        try:
            text = path.read_text(encoding='utf-8')
            meta = frontmatter(text)
            if path.name == 'index.md':
                expected = {'okf_version': '0.2'} if path.parent == root else None
                if meta != expected:
                    raise ValueError('index metadata must be root-only okf_version: "0.2"')
            elif path.name == 'log.md':
                if meta is not None:
                    raise ValueError('logs must not have frontmatter')
                headings = re.findall(r'^## (.+)$', text, re.M)
                if not headings:
                    raise ValueError('log needs date headings')
                dates = [datetime.date.fromisoformat(h) for h in headings]
                if dates != sorted(dates, reverse=True):
                    raise ValueError('log dates must be newest first')
            else:
                if not meta or not isinstance(meta.get('type'), str) or not meta['type'].strip():
                    raise ValueError('concept requires nonempty string type')
                if 'status' in meta and meta['status'] not in ('draft', 'stable', 'deprecated'):
                    raise ValueError('invalid lifecycle status')
        except (ValueError, UnicodeError, yaml.YAMLError) as error:
            errors.append(f'{path}: {error}')
    for directory in sorted(directories):
        for name in ('index.md', 'log.md'):
            if not (directory / name).is_file():
                errors.append(f'{directory}: missing {name}')
        index = directory / 'index.md'
        if index.is_file():
            text = index.read_text()
            for child in directory.iterdir():
                target = child.name + '/index.md' if child in directories else child.name
                if (child in directories or child.suffix == '.md') and child.name != 'index.md':
                    if f']({target})' not in text:
                        errors.append(f'{index}: unlisted {target}')
    return errors


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('bundle', type=Path)
    args = parser.parse_args()
    errors = check(args.bundle.resolve())
    if errors:
        print('\n'.join(errors), file=sys.stderr)
        sys.exit(1)
    print(f'OKF structure passes: {args.bundle}')
