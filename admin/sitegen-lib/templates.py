from collections import OrderedDict
from jinja2 import Environment, FileSystemLoader
from itertools import groupby
import os
import datetime

from config import *
import terminal

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
	for entry, attributes in entries.items():
		for topic in attributes['topic']:
			tree.add_to_topic([str.strip() for str in topic.split('/')], entry)
	return tree


class Builder(object):
	"""Contains environment for building webpages from templates"""

	def __init__(self, template_dir, root_output_dir, entries, afp_entries,
		is_devel):
		self.j2_env = Environment(loader = FileSystemLoader(template_dir),
			trim_blocks=True)
		# pass functions to environment for use in templates
		self.prepare_env()
		self.root_output_dir = root_output_dir
		#TODO: use only afp_entries
		self.entries = entries
		self.afp_entries = afp_entries
		self.is_devel = is_devel

	def prepare_env(self):
		def startswith(value, beginning):
			return value.startswith(beginning)
		def datetimeformat(value, format='%Y-%m-%d'):
			return value.strftime(format)
		def rfc822(value):
			# Locale could be something different than english, to prevent printing
			# non english months, we use this fix
			month = "Jan Feb Mar Apr May Jun Jul Aug Sep Oct Nov Dec".split(" ")[value.month - 1]
			return value.strftime("%d " + month + " %Y %T %z")
		def split(value):
			return value.split()
		def short_month(value):
			return "jan feb mar apr may jun jul aug sep oct nov dec".split(" ")[value - 1]
		self.j2_env.filters['startswith'] = startswith
		self.j2_env.filters['datetimeformat'] = datetimeformat
		self.j2_env.filters['rfc822'] = rfc822
		self.j2_env.filters['split'] = split
		self.j2_env.filters['short_month'] = short_month

	def write_file(self, filename, template, values):
		# UTF-8 hack because of different string handling in python 2 vs 3
		with open(os.path.join(self.root_output_dir, filename), 'wb') as f:
			f.write(template.render(values).encode('utf8'))

	def generate_standard(self, filename, template_name):
		template = self.j2_env.get_template(template_name)
		self.write_file(filename, template, {})
		terminal.success("Generated {}".format(filename))

	def generate_topics(self):
		template = self.j2_env.get_template("topics.tpl")
		tree = collect_topics(self.entries)
		self.write_file("topics.shtml", template, {'tree': tree})
		terminal.success("Generated topics.shtml")

	def generate_index(self):
		template = self.j2_env.get_template("index.tpl")
		#TODO: use groupby
		by_year = dict()
		for e in self.afp_entries.values():
			try:
				by_year[e.publish_date.year].add(e)
			except KeyError:
				by_year[e.publish_date.year] = {e}
		for y in by_year:
			by_year[y] = sorted(by_year[y], key = lambda e: (e.publish_date,
				e.name), reverse=True)
		self.write_file("index.shtml", template,
			{'by_year': by_year, 'is_devel': self.is_devel})
		terminal.success("Generated index.shtml")

	def generate_entries(self):
		counter = 0
		template = self.j2_env.get_template("entry.tpl")
		for name, entry in self.afp_entries.items():
			#TODO: Solve more elegantly
			entry.imports = sorted(entry.imports, key = lambda x: x.name)
			entry.used = sorted(entry.used, key = lambda x: x.name)
			self.write_file(os.path.join("entries", name + ".shtml"), template,
				{'entry': entry, 'is_devel': self.is_devel})
			counter += 1
		for name, entry in self.afp_entries.no_index.items():
			self.write_file(os.path.join("entries", name + ".shtml"), template,
				{'entry': entry, 'is_devel': self.is_devel})
			counter += 1
		terminal.success("Generated shtml files for {:d} entries".format(counter))

	def generate_download(self):
		template = self.j2_env.get_template("download.tpl")
		self.write_file("download.shtml", template,
			{'today': datetime.datetime.now().strftime("%Y-%m-%d"),
			'is_devel': self.is_devel})
		terminal.success("Generated download.shtml")

	def generate_statistics(self):
		#TODO: simplify with itertools
		# Count loc and articles per year
		articles_years = dict()
		loc_years = dict()
		for article in self.afp_entries.values():
			try:
				articles_years[article.publish_date.year] += 1
				loc_years[article.publish_date.year] += article.loc
			except KeyError:
				articles_years[article.publish_date.year] = 1
				loc_years[article.publish_date.year] = article.loc
		# Count new authors per year
		author_years = dict()
		for author in self.afp_entries.authors.values():
			first_year = min([e.publish_date.year for e in author.articles])
			try:
				author_years[first_year] += 1
			except KeyError:
				author_years[first_year] = 1
		# Build cumulative values
		author_years_cumulative = author_years.copy()
		for y in sorted(articles_years)[1:]:
			articles_years[y] += articles_years[y - 1]
			loc_years[y] += loc_years[y - 1]
			author_years_cumulative[y] += author_years_cumulative[y - 1]
		# Find 10 most imported entries, entries with the same number of
		# imports share one place.
		most_used = sorted([a for a in self.afp_entries.values()],
			key = lambda x: (-len(x.used), x.name))
		# Show more than 10 articles but not more than necessary
		i = 0
		while(i < 10 or len(most_used[i].used) == len(most_used[i + 1].used)):
			i += 1
		most_used = groupby(most_used[:i + 1], key = lambda x: len(x.used))
		articles_by_time = sorted(self.afp_entries.values(),
			key = lambda x: x.publish_date)
		articles_by_time1 = groupby(articles_by_time,
			key = lambda x: x.publish_date.year)
		template = self.j2_env.get_template("statistics.tpl")
		self.write_file("statistics.shtml", template,
			{'entries': self.afp_entries,
			'num_lemmas': sum([a.lemmas for a in self.afp_entries.values()]),
			'num_loc': sum([a.loc for a in self.afp_entries.values()]),
			'years': sorted(articles_years),
			'articles_year': [articles_years[y] for y in sorted(articles_years)],
			'loc_years': map(lambda x: round(x, -2),
				[loc_years[y] for y in sorted(loc_years)]),
			'author_years': [author_years[y] for y in sorted(author_years)],
			'author_years_cumulative': [author_years_cumulative[y] for y in
				sorted(author_years_cumulative)],
			'most_used': most_used,
			'articles_by_time': articles_by_time,
			'articles_by_time1': articles_by_time1})
		terminal.success("Generated statistics.shtml")

	def generate_status(self, build_data):
		template = self.j2_env.get_template("status.tpl")
		self.write_file("status.shtml", template,
			{'entries': [self.afp_entries[e]
				for e in sorted(self.afp_entries)],
			'build_data': build_data})
		terminal.success("Generated status.shtml")

	def generate_rss(self, num_entries):
		template = self.j2_env.get_template("rss.tpl")
		entries = sorted(self.afp_entries.values(),
				key = lambda e: (e.publish_date, e.name), reverse=True)
		self.write_file("rss.xml", template, {'entries': entries[:num_entries]})
		terminal.success("Generated rss.xml")

