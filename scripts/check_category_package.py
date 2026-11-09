#!/usr/bin/env python3
"""Check that category specifications are a definition-only, HOL-only package."""
import argparse
import re
from pathlib import Path


def check(package):
    theories = {p.stem: p for p in package.glob('*.thy')}
    assert theories, 'no specification theories'
    root = (package / 'ROOT').read_text()
    assert re.search(r'session\s+Category_Specifications\s*=\s*HOL\s*\+', root), 'unexpected session parent'
    assert 'quick_and_dirty = false' in root, 'normal proof checking must be explicit'
    assert not (package / 'ROOTS').exists(), 'the package must not discover sibling sessions'
    assert not any(p.is_dir() for p in package.iterdir()), 'unexpected nested package'
    listed = root.split('  theories\n', 1)[1].split()
    assert set(listed) == set(theories) and len(listed) == len(theories), 'ROOT inventory mismatch'
    graph = {}
    forbidden = r'^(?:lemma|theorem|corollary|proposition|proof|ML\w*|setup|axiomatization|oracle|sorry|oops|interpretation|lemmas)\b'
    for name, path in theories.items():
        text = path.read_text()
        imports = re.search(r'\bimports\s+(.*?)\bbegin\b', text, re.S)
        assert imports, f'{name}: no imports'
        deps = imports.group(1).split()
        assert all(d == 'Main' or d in theories for d in deps), f'{name}: external import {deps}'
        graph[name] = [d for d in deps if d != 'Main']
        commands = re.sub(r'\(\*.*?\*\)', '', text, flags=re.S)
        commands = re.sub(r'\\<open>.*?\\<close>', '', commands, flags=re.S)
        commands = re.sub(r'"(?:[^"\\]|\\.)*"', '', commands, flags=re.S)
        assert not re.search(forbidden, commands, re.M), f'{name}: non-specification command'
    def visit(name, active, seen):
        assert name not in active, f'import cycle at {name}'
        if name not in seen:
            for dep in graph[name]:
                visit(dep, active | {name}, seen)
            seen.add(name)
    seen = set()
    for name in theories:
        visit(name, set(), seen)
    for link in re.findall(r'\]\(([^)]+)\)', (package / 'README.md').read_text()):
        target = (package / link).resolve()
        assert target.is_relative_to(package.resolve()) and target.is_file(), f'nonlocal or broken reading-guide link: {link}'
    print(f'Category package passes: {len(theories)} definition-only theories; all imports are local or HOL Main')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('package', nargs='?', type=Path,
                        default=Path(__file__).resolve().parents[1] / 'thys/Category_Specifications')
    check(parser.parse_args().package)


if __name__ == '__main__':
    main()
