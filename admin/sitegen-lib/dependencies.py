"""
The dependencies of an AFP entry are listed in the ROOT file, and as it
is regular, this script uses a regular expression to extract the dependencies
and adds them to the JSON file of the entry.
"""
import json
import os

from write_file import write_file


def add_dependencies(entries_dir, dependencies_file):
    """For each entry in the thys/ directory, extract the dependencies and add
    them to the JSON file."""

    with open(dependencies_file) as dep:
        dependencies = json.load(dep)

    for entry in os.listdir(entries_dir):
        shortname = entry[:-3]
        entry_deps = dependencies[shortname]
        afp_deps = entry_deps["afp_deps"]

        data = {"dependencies": afp_deps}
        write_file(os.path.join(entries_dir, entry), data)
