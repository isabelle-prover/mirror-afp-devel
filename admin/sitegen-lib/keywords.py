"""Generates a list of keywords for the search autocomplete using RAKE."""
import RAKE


def print_keywords(text):
    rake = RAKE.Rake(RAKE.SmartStopList())
    res = rake.run(text, minCharacters=3, maxWords=2, minFrequency=1)
    for keyword in res:
        print(keyword)
