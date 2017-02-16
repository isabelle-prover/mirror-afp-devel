from datetime import datetime
import os.path
import pytz
import re

#TODO: script relies on checking paths, can this be broken?

def normpath(path, *paths):
    try:
        return os.path.abspath(os.path.join(path, *paths))
    # only happens in python version < 3, non ascii cant be part of a path
    except UnicodeDecodeError:
        return None

def format_lib_src(libstr):
    if libstr.startswith("HOL/Library"):
        return libstr[4:]
    elif libstr.startswith("HOL/"):
        return libstr.split("/")[1]
    elif libstr.startswith("Tools/"):
        return '/'.join(libstr.split("/")[0:2])
    else:
        return libstr

class afp_author:
    """An AFP author has a name and a web or mail address"""
    def __init__(self, name, address):
        self.name = name
        self.address = address
        self.articles = set()

    def __eq__(self, other):
        return self.name == other.name

    def __hash__(self):
        return hash(self.name)

class afp_entry:
    """An AFP entry consists of metadata (date, authors, etc), used imports,
       used library imports, paths to thys files and which AFP entries import
       it.
       Not all of this data is present after initialization. See also class
       afp_dict.
       It still relies on information created by the entries-dict in sitegen.py.
       """
    def __init__(self, name, entry_dict, afp_dict, no_index = False):
        self.name = name
        self.afp_dict = afp_dict
        self.path = os.path.join(self.afp_dict.path, self.name)
        self.title = entry_dict['title']
        #TODO: fix author generation, Contributors???
        self.authors = []
        for name, _address in entry_dict['author']:
            self.authors.append(afp_dict.authors[name])
            if not no_index:
                afp_dict.authors[name].articles.add(self)
        self.publish_date = datetime.strptime(entry_dict['date'], "%Y-%m-%d")
        #add UTC timezone to date
        self.publish_date = self.publish_date.replace(tzinfo = pytz.UTC)
        self.abstract = entry_dict['abstract']
        self.license = entry_dict['license']
        self.releases = list(entry_dict['releases'].items())
        self.contributors = (entry_dict['contributors']
                             if entry_dict['contributors'][0][0] else [])
        self.extra = entry_dict['extra']
        self.thys = set()
        self.status = None
        for root, _dirnames, filenames in os.walk(self.path):
            for f in filenames:
                if f.endswith(".thy"):
                    self.thys.add(os.path.join(self.path, root, f))

    def __str__(self):
        return self.name

    def __repr__(self):
        return self.name

    def import_article(self, imp):
        if self.name != imp.name:
            self.imports.add(imp)

    def add_imports(self):
        self.imports = set()
        self.add_theory_dependencies()
        self.add_root_dependencies()

    def add_theory_dependencies(self):
        # every word between "imports" and "begin" is checked if it could be
        # refering to .thy-file in the afp
        # there is definitely a much better way to do this :P
        pattern0 = re.compile("imports(.*?)begin", re.DOTALL)
        self.imports = set()
        for t in self.thys:
            # we read the whole file to match everything between "imports" and
            # "begin" even newlines
            with open(t, 'r') as c:
                content = c.read()
            match0 = pattern0.search(content)
            if match0 is not None:
                imps = [normpath(os.path.dirname(t), x.strip("\"' ") + ".thy")
                        for x in match0.group(1).split()]
                for i in imps:
                    try:
                        self.import_article(self.afp_dict.all_thys[i])
                    except KeyError:
                        pass

    def add_root_dependencies(self):
        root = os.path.join(self.path, "ROOT")
        with open(root, 'r') as root_file:
            root_content = root_file.read()
        for line in root_content.splitlines():
            if line.startswith("session"):
                for word in [x.strip("\"' \t") for x in line.split()]:
                    try:
                        self.import_article(self.afp_dict[word])
                    except KeyError:
                        pass
        for word in [x.strip("\"' \t") for x in root_content.split()]:
            theory = normpath(self.path, word + ".thy")
            try:
                self.import_article(self.afp_dict.all_thys[theory])
            except KeyError:
                pass

    def add_lib_imports(self):
        self.lib_imports = set()
        self.add_root_lib_dependencies()
        self.add_theories_lib_dependencies()

    def add_theories_lib_dependencies(self):
        pattern0 = re.compile("imports(.*?)begin", re.DOTALL)
        pattern1 = re.compile("^~~/src/(.*)")
        for thy in self.thys:
            with open(thy, 'r') as content_file:
                content = content_file.read()
            match0 = pattern0.search(content)
            if match0 is not None:
                imps = [x.strip("\"' \t") for x in match0.group(0).split()]
                for word in imps:
                    match1 = pattern1.search(word)
                    if match1 is not None:
                        self.lib_imports.add(format_lib_src(match1.group(1)))


    def add_root_lib_dependencies(self):
        pattern0 = re.compile("^~~/src/(.*)")
        pattern1 = re.compile("^session.*= (.*) \+")
        with open(os.path.join(self.path, "ROOT"), 'r') as r:
            root_content = r.read()
        for word in [x.strip("\"' \t") for x in root_content.split()]:
            match0 = pattern0.search(word)
            if match0 is not None:
                self.lib_imports.add(format_lib_src(match0.group(1)))
        with open(os.path.join(self.path, "ROOT"), 'r') as r:
            for line in r:
                match1 = pattern1.search(line)
                if match1 is not None:
                    lib = match1.group(1).strip("\"' \t")
                    if (lib.startswith("HOL-") and not lib.endswith("Library")):
                        self.lib_imports.add(lib[4:])

    def add_loc(self):
        """Count non empty lines in thy-files"""
        self.loc = 0
        for t in self.thys:
            with open(t, 'r') as f:
                for l in f:
                    if l.strip():
                        self.loc += 1

    def add_number_of_lemmas(self):
        """Count number of lemmas, theorems and corollarys"""
        self.lemmas = 0
        for t in self.thys:
            with open(t, 'r') as f:
                for l in f:
                    if l.startswith("lemma") or l.startswith("corollary") or \
                       l.startswith("theorem"):
                        self.lemmas += 1


class afp_dict(dict):
    """The afp_dict contains all afp_entry(s) and a list of afp_author(s).
       To create import/export data for all afp_entrys call build_stats().
    """
    def __init__(self, entries, afp_thys_path, *args):
        dict.__init__(self, *args)
        self.path = normpath(afp_thys_path)
        self.authors = dict()
        # Extra dict for entries which don't show up in index and statistics
        #TODO: document how it works, improve how it works
        self.no_index = dict()
        for entry in entries.values():
            for name, address in entry['author']:
                self.authors[name] = afp_author(name, address)
        for name, entry in entries.items():
            if 'extra' in entry and 'no-index' in entry['extra']:
                self.no_index[name] = afp_entry(name, entry, self,
                                                no_index = True)
            else:
                self[name] = afp_entry(name, entry, self)
        for name in self.no_index.keys():
            del entries[name]
        # all_thys is a dict which maps a thy file to its corresponding AFP
        # entry
        self.all_thys = dict()
        for a in self:
            for t in self[a].thys:
                self.all_thys[t] = self[a]

    def build_stats(self):
         for _k, a in self.items():
             a.add_imports()
             a.add_lib_imports()
             a.add_loc()
             a.add_number_of_lemmas()
             a.used = set()
         for _k, a in self.items():
             for i in a.imports:
                 i.used.add(a)

