"""Generates a list of keywords for the search autocomplete. Each entry’s 
abstract is sanitised and then the keywords are extracted with the RAKE 
algorithm.
"""
import json
import os
import re
from itertools import groupby

import unidecode
from rake_nltk import Rake
import nltk

nltk.download('stopwords')
nltk.download('punkt')


def generate_keywords(entries_dir):
    """RAKE is used to extract the keywords from every abstract. 
    
    The top 8 keywords are added to a list of all keywords and the keywords 
    that appear in more than two abstracts are preserved. Finally, plurals 
    are removed."""

    rake_object = Rake(max_length=2)

    replacements = [
        (r"\s+", " "),
        (r"<.*?>", ""),
        (r"[^\w\s/.()',-]", " "),
        (r"\s+", " "),
    ]

    keywords = []

    for entry in os.listdir(entries_dir):
        with open(os.path.join(entries_dir, entry)) as json_file:
            data = json.load(json_file)
            text = data["abstract"]

        for old, new in replacements:
            text = re.sub(old, new, text)

        text = unidecode.unidecode(text)

        rake_object.extract_keywords_from_text(text)
        keywords.extend(rake_object.get_ranked_phrases())

    # keep keywords that appear in 2 or more abstracts
    keywords = [i for i, c in groupby(sorted(keywords)) if len(list(c)) > 1]

    # remove plurals if we have the singular
    for keyword in keywords:
        if keyword + "s" in keywords:
            keywords.remove(keyword + "s")

    return [{"id": i, "keyword": x} for i, x in enumerate(keywords)]
