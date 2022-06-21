"""
Most the statistics for the site, are generated by Hugo. This script, 
generates other statistics like number of lines in the AFP using the 
scripts from the current AFP. 

For this script to work, `return data` needs to be added at 
line 212 in templates.py
"""

import os

import afpstats
import metadata
import templates
from config import options
from sitegen import associate_releases, parse, read_versions
from write_file import write_file


def add_statistics(base_dir, thys_dir, data_dir):
    """Creates the necessary objects to generates the statistics, 
    then outputs them to the data directory"""
    options.templates_dir = os.path.join(base_dir, "metadata", "templates")
    options.dest_dir = data_dir

    entries = parse(os.path.join(base_dir, "metadata", "metadata"))
    versions = read_versions(os.path.join(base_dir, "metadata", "release-dates"))
    associate_releases(entries, versions, os.path.join(base_dir, "metadata", "releases"))

    deps_dict = metadata.empty_deps(entries)

    afp_dict = afpstats.afp_dict(entries, thys_dir, deps_dict)
    afp_dict.build_stats()
    builder = templates.Builder(options, entries, afp_dict)

    stats = builder.generate_statistics()

    loc_articles = [article.loc for article in stats["articles_by_time"]]

    all_articles = [a.name for a in stats["articles_by_time"]]

    data = {
        "num_lemmas": stats["num_lemmas"],
        "num_loc": stats["num_loc"],
        "articles_year": stats["articles_year"],
        "loc_years": stats["loc_years"],
        "author_years": stats["author_years"],
        "author_years_cumulative": stats["author_years_cumulative"],
        "loc_articles": loc_articles,
        "all_articles": all_articles,
    }

    write_file(os.path.join(data_dir, "statistics.json"), data)