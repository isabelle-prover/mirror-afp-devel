from collections import OrderedDict
from operator import itemgetter
import os

from config import *


### topics

class Tree(object):
	def __init__(self):
		self.subtopics = OrderedDict()
		self.entries = []

	def add_topic(self, topic):
		if len(topic) > 0:
			if topic[0] not in self.subtopics:
				tree = Tree()
				self.subtopics[topic[0]] = tree
			else:
				tree = self.subtopics[topic[0]]
			tree.add_topic(topic[1:])

	def add_to_topic(self, topic, entry):
		if len(topic) > 0:
			if topic[0] not in self.subtopics:
				warn(u"In entry {0}: unknown (sub)topic {1}".format(entry, topic))
			else:
				self.subtopics[topic[0]].add_to_topic(topic[1:], entry)
		else:
			self.entries.append(entry)

	def __str__(self):
		return self._to_str()

	def _to_str(self, indent = 0):
		indent_str = ' ' * indent
		result = indent_str + str(self.entries) + "\n"
		for subtopic, tree in self.subtopics.items():
			result += indent_str
			result += subtopic
			result += "\n"
			result += tree._to_str(indent + 2)
		return result

def read_topics(filename):
	tree = Tree()
	stack = []
	with open(filename) as input:
		for line in input:
			count = 0
			while line[count] == ' ':
				count += 1
			if count % 2:
				raise Exception(u"Illegal indentation at line '{0}'".format(line))
			level = count // 2
			if level <= len(stack):
				stack = stack[0:level]
			else:
				raise Exception(u"Illegal indentation at line '{0}'".format(line))
			stack.append(line[count:len(line)-1])
			tree.add_topic(stack)
	return tree

# for topics page: group entries by topic
def collect_topics(entries):
	tree = read_topics(os.path.join(options.metadata_dir, "topics"))
	for entry, attributes in entries:
		for topic in attributes['topic']:
			tree.add_to_topic([str.strip() for str in topic.split('/')], entry)
	return tree

def generate_link_list(entries):
	return ''.join([html_topic_link.format(e) for e in entries])

# HTML formatting for topics page
def generate_topics(entries):
	def _gen(tree, level):
		result = ""
		if level <= html_until_level:
			if len(tree.entries) > 0:
				result += html_topic_link_list.format(generate_link_list(tree.entries))
			for topic, subtree in tree.subtopics.items():
				result += html_topic_headings[level].format(topic)
				if level < html_until_level:
					result += _gen(subtree, level + 1)
				else:
					result += html_topic_link_list.format(_gen(subtree, level + 1))
		else:
			result = generate_link_list(tree.entries)
			for topic, subtree in tree.subtopics.items():
				result += html_topic_headings[level].format(topic)
				result += _gen(subtree, level + 1)

		return result

	tree = collect_topics(entries)
	return _gen(tree, 0)


### index

# takes a list of author-URL pairs and formats a string, either with
# or without email addresses
def generate_author_list(authors, spacer, last_spacer, ignore_mail = True, ignore_url = False):
	def _to_str(author):
		name, url = author
		if url and not ignore_url:
			if url.startswith("mailto:"):
				if ignore_mail:
					return name
				else:
					return u"{0} ({1})".format(name, url[7:])
			return html_author_link.format(url, name)
		else:
			return name

	authors = list(map(_to_str, authors))
	if len(authors) == 0:
		return ""
	elif len(authors) == 1:
		return authors[0]
	else:
		return u"{0}{1}{2}".format(
		  spacer.join(authors[:len(authors)-1]),
		  last_spacer,
		  authors[len(authors)-1]
		)

# group entries by year
def collect_years(entries):
	extracted = [
		(attributes['date'] if attributes['date'] != '' else 'unknown', entry, attributes)
		for entry, attributes in entries
	]
	extracted.sort(key = itemgetter(0), reverse = True)
	years = OrderedDict()
	for date, entry, attributes in extracted:
		key = date[0:4] if date != 'unknown' else date
		if key in years:
			years[key].append((entry, attributes))
		else:
			years[key] = [(entry, attributes)]
	return years.items()

def generate_index(entries, param):
	if param == "devel":
		if options.is_devel():
			return html_index_devel
		else:
			return html_index_stable
	elif param == "table":
		years = collect_years(entries)
		result = ""
		for year, list in years:
			rows = ""
			for entry, attributes in list:
				rows += html_index_entry.format(
					attributes['date'],
					entry,
					attributes['title'] if attributes['title'] != '' else entry,
					generate_author_list(attributes['author'], ",\n", " and \n")
				)
			result += html_index_year.format(year, rows)
		return result
	else:
		raise Exception("In generator 'index': Unknown parameter "+param)


### entry

# Extracts parts of a date, used in the bibtex files
def month_of_date(date):
	return "jan feb mar apr may jun jul aug sep oct nov dec".split(" ")[int(date.split("-")[1]) - 1]

def year_of_date(date):
	return date.split("-")[0]

def format_entry_text(title, text):
	return html_entry_text_wrapper.format(
		title, "\n" + text
	)

def format_entry_pre_text(title, text):
	return html_entry_pre_text_wrapper.format(
		title, text
	)

def depends_on_string(deps):
	sorted_deps = list(deps)
	sorted_deps.sort()
	return ', '.join(html_entry_link.format(dep, dep + ".shtml") for dep in sorted_deps)

def format_depends_on(deps):
	return html_entry_depends_on_wrapper.format(depends_on_string(deps)) if len(deps) > 0 else ''

def format_used_by(deps):
	return html_entry_used_by_wrapper.format(depends_on_string(deps)) if len(deps) > 0 else ''

def format_opt_contributors(contributors):
	if contributors == [("", None)]:
		return ""
	else:
		return html_contributors.format(generate_author_list(contributors, ', ', ' and ', ignore_mail = False))

def format_status(attributes):
	return html_entry_status_wrapper.format(attributes['status']) if options.is_devel() else ''

# HTML formatting for entry page
# supports the following parameters:
#   'header' for entry header (author, title, date etc.)
#   'older' for list of older releases
def generate_entry(entry, attributes, param):
	if param == "header":
		result = ""
		capitalized_title = ""
		for word in [str.strip() for str in attributes['title'].split(' ')]:
			if len(word) > 0 and word[0].isupper():
				capitalized_title += html_entry_capitalized.format(word[0], word[1:])
			else:
				capitalized_title += word + "\n"
		result += html_entry_heading.format(capitalized_title)

		text_columns = format_entry_text("Abstract", attributes['abstract'])
		text_columns += "".join([format_entry_text(k, v) for k, v in attributes['extra'].values()])
		text_columns += format_entry_pre_text("BibTeX",
			bibtex_wrapper.format(
				entry,
				generate_author_list(attributes['author'], ' and ', ' and ', ignore_url = True),
				attributes['title'],
				month_of_date(attributes['date']),
				year_of_date(attributes['date']))
		)

		result += html_entry_header_wrapper.format(
			attributes['title'],
			generate_author_list(attributes['author'], ', ', ' and ', ignore_mail = False),
			format_opt_contributors(attributes['contributors']),
			attributes['date'],
			text_columns,
			html_license_link.format(attributes['license'][0], attributes['license'][1]),
			entry,
			format_depends_on(attributes['depends-on']),
			format_used_by(attributes['used-by']),
			format_status(attributes)
		)
	elif param == "older":
		if options.is_devel():
			return ""

		if len(attributes['releases']) > 1:
			str = ""
			for version, release_dates in list(attributes['releases'].items())[1:]:
				str += "".join(html_entry_older_release.format(version, release_date) for release_date in release_dates)
			result = html_entry_older_list.format(str)
		else:
			result = "None"

		result = html_entry_older_wrapper.format(result)
	else:
		raise Exception("In generator 'entry': Unknown parameter "+param)

	return result


### status

def generate_status(entries, param, build_data):
	if param == "header":
		return html_status_header.format(
			build_data['isabelle_id'],
			build_data['afp_id'],
			build_data['time'],
			build_data['url'],
			build_data['job']
		)
	elif param == "table":
		rows = ""
		for entry, attributes in sorted(entries):
			rows += html_status_entry.format(attributes['status'], entry)

		return rows
	else:
		raise Exception("In generator 'status': Unknown parameter "+param)


### download

def generate_download(entries):
	if options.is_devel():
		return ""

	else:
		return html_download_stable

### statistics

def generate_statistics(entries):
	i = 1
	num_of_imports = -1
	most_used = ""
	# Put articles with same number of imports on same position
	for (n, l) in STAT_FIGURES['most_used10']:
		pos = (str(i) + "." if num_of_imports != l else "")
		i += (1 if num_of_imports != l else 0)
		num_of_imports = l
		most_used += html_most_used_table_row.format(pos = pos, name = n, num = l)
	return html_statistics_text_wrapper.format(
			loc = int(round(STAT_FIGURES['loc'], -2)),
			num_articles = len(entries),
			num_lemmas = int(round(STAT_FIGURES['num_lemmas'], -2)),
			num_authors = STAT_FIGURES['num_authors'],
			years = "["
			         + ", ".join([str(y) for y in 
			                      sorted(STAT_FIGURES['articles_years'])])
			         + "]",
			no_articles = "["
			              + ", ".join([str(STAT_FIGURES['articles_years'][y])
			                           for y
			                           in sorted(STAT_FIGURES['articles_years'])])
			              + "]",
			no_loc = "["
			         + ", ".join([str(round(STAT_FIGURES['loc_years'][y], -2))
			                      for y in sorted(STAT_FIGURES['loc_years'])])
			         + "]",
			no_authors = "["
			             + ", ".join([str(STAT_FIGURES['author_years'][y])
			                          for y in sorted(STAT_FIGURES['author_years'])])
			             + "]",
			no_authors_series = "["
			                    + ", ".join([str(STAT_FIGURES['author_years_series'][y])
			                                 for y
			                                 in sorted(STAT_FIGURES['author_years_series'])])
			                    + "]",
			most_used = most_used,
			all_articles = "['" + "','".join(STAT_FIGURES['all_articles']) + "']",
			loc_articles = "[" + ",".join(map(str, STAT_FIGURES['loc_articles'])) + "]",
			years_loc_articles = "[" + ",".join(map(str, STAT_FIGURES['years_loc_articles'])) + "]"
			)


# key : (path, generator, for-each)
#   'key' denotes the filename of the template (without suffix)
#   'path' denotes the destination sub-path for generated files
#   'generator' is the generating function for the data of the template. The
#     parameters this function will get is determined by 'for-each'.
#   'for-each' determines generation behaviour: if set to None, one file
#     will be generated for all entries together and the 'generator' function will
#     receive a list of all entries. Otherwise, a function expression
#     is expected which gets the entry name and returns a filename to store the
#     result in (without suffix) and the 'generator' function will get just one
#     entry name and its attributes
#   'devel' indicates that the generator should only be invoked when in devel
#     mode, i.e. if a build status file is present
templates = {
	'topics': ('.', generate_topics, None, False),
	'index': ('.', generate_index, None, False),
	'entry': ('./entries', generate_entry, lambda entry: entry, False),
	'download': ('.', generate_download, None, False),
	'status': ('.', generate_status, None, True),
	'statistics': ('.', generate_statistics, None, False)
}
