"""
This script generates related entries, using three metrics:
    * Sharing dependencies
    * Sharing keywords
    * Sharing keywords

These are weighted and used to find entries which are likely similar.

These are then added to the entries to improve site navigation.
"""
import json
import os

from keywords import generate_keywords
from write_file import write_file


def add_related(entries_dir):
    """
    First three dictionaries are created as follows:

    dependencies = {"dependency": [list-of-entries, ...], ...}
    keywords = {"keyword": [list-of-entries, ...], ...}
    topics = {"topic": [list-of-entries, ...], ...}

    Keywords that feature in more than 10 entries are dropped. Then
    a dictionary is created with the relatedness scores between each
    entry. Finally, the top three related entries are chosen for each
    entry.
    """

    keywords = {}

    for obj in generate_keywords(entries_dir):
        keywords[obj["keyword"]] = []


    dependencies = {}
    topics = {}
    for entry in os.listdir(entries_dir):
        shortname = entry[:-3]

        with open(os.path.join(entries_dir, entry)) as file:
            data = json.load(file)
            if "dependencies" in data:
                for dep in data["dependencies"]:
                    if dep in dependencies:
                        dependencies[dep].append(shortname)
                    else:
                        dependencies[dep] = [shortname]
            if "topics" in data:
                for topic in data["topics"]:
                    if topic in topics:
                        topics[topic].append(shortname)
                    else:
                        topics[topic] = [shortname]
            for keyword in keywords.keys():
                if keyword in data["abstract"].lower():
                    keywords[keyword].append(shortname)

    for keyword, values in list(keywords.items()):
        if len(values) > 10:
            keywords.pop(keyword)

    related_entries = {}

    for dataSet in [(keywords, 1), (dependencies, 1.5), (topics, 0.5)]:
        populate_related(dataSet[0], related_entries, dataSet[1])

    for entry in related_entries:
        for keyword, value in list(related_entries[entry].items()):
            if value <= 2.5:
                related_entries[entry].pop(keyword)

    final_related = {}

    for keyword, values in related_entries.items():
        final_related[keyword] = top_three(values)

    for entry, related in final_related.items():
        if related:
            data = {"related": related}
            write_file(os.path.join(entries_dir, entry + ".md"), data)


def populate_related(data, related, modifier=1):
    """This is a heavily nested loop to create the relatedEntries dictionary.

    For each of the categories, the list of entries associated with
    each key is iterated over twice and, if the entries are not the
    same, the modifier of that category is added to the relatedness
    score between the two entries in the dictionary. As the loop
    iterates twice over the value set, the resulting dictionary is
    bijective — i.e., the value for A->B will be equal to B->A.
    """
    for _, entries in data.items():
        for keyEntry in entries:
            for valueEntry in entries:
                if valueEntry != keyEntry:
                    if keyEntry in related:
                        if valueEntry in related[keyEntry]:
                            related[keyEntry][valueEntry] += modifier
                        else:
                            related[keyEntry][valueEntry] = modifier
                    else:
                        related[keyEntry] = {valueEntry: modifier}


def top_three(dictionary):
    """Returns the highest three dictionary keys by value"""
    return sorted(dictionary, key=dictionary.get, reverse=True)[:3]
