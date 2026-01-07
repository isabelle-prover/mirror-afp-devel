/* constants */

const NUM_MAX_SIDE_RESULTS = 4
const NUM_MAX_MAIN_RESULTS = 15

const ID_SEARCH_BUTTON = 'search-button'
const ID_RESULTS_ENTRIES = 'search-results'
const ID_RESULTS_AUTHORS = 'author-results'
const ID_RESULTS_TOPICS = 'topic-results'


/* index */

function build_indexes(entries, authors, topics, keywords) {
  const entry_index = new FlexSearch.Document({
    encoder: 'advanced',
    tokenize: 'forward',
    document: {
      index: ['shortname', 'title', 'abstract', 'topics[]', 'authors[]'],
      store: true,
    },
  })
  entries.forEach((entry, id) => entry_index.add(id, entry))

  const author_index = new FlexSearch.Document({
    encoder: 'advanced',
    tokenize: 'forward',
    document: {
      index: 'name',
      store: true
    },
  })
  authors.forEach((author, id) => author_index.add(id, author))

  const topic_index = new FlexSearch.Document({
    encoder: 'icase',
    tokenize: 'forward',
    document: {
      index: 'name',
      store: true
    },
  })
  topics.forEach((topic, id) => topic_index.add(id, topic))

  const suggest_index = get_suggest_index(keywords)

  return {
    entry: entry_index,
    author: author_index,
    topic: topic_index,
    suggest: suggest_index,
  }
}


/* search */

function local_search(indices, query) {
  const entry_results = [...new Set(indices['entry'].search(query, NUM_MAX_MAIN_RESULTS + 1,
    {enrich: true}).flatMap(e => e.result).map(d => d.doc))]
  const topic_results = indices['topic'].search(query, NUM_MAX_SIDE_RESULTS + 1,
    {enrich: true, pluck: 'name'}).map(d => d.doc)
  const author_results = indices['author'].search(query, NUM_MAX_SIDE_RESULTS + 1,
    {enrich: true, pluck: 'name'}).map(d => d.doc)
  return {entries: entry_results, topics: topic_results, authors: author_results}
}


/* result handling */

function render_entry(entry) {
  const authors = entry.authors.join(', ')
  const topics = entry.topics.map((topic, key) =>
    `<a href='${entry.topic_links[key]}'>${topic}</a>`).join(', ')
  const year = entry.year

  return `
  <div>
    <div class='title'>
      <h3>
        <a href='${entry.link}'>${entry.title}</a>
      </h3>
    </div>
    <div class='subtitle'>
      <span style="float:left">${authors}</span>
      <span style="float:right">${year}</span>
    </div>
    <div class='abstract mathjax_process'>${entry.abstract}</div>
    <div>in ${topics}</div>
  </div>`
}

function render_entries_results(parent, data, query) {
  if (!data) parent.replaceChildren(parse_elem('<p>Please enter a search term above.</p>'))
  else if (data.length === 0) parent.replaceChildren(parse_elem('<p>No results.</p>'))
  else {
    const end = data.length > NUM_MAX_MAIN_RESULTS ? '...' : ''
    const res = parse_elem(`
      ${data.slice(0, NUM_MAX_MAIN_RESULTS).map(entry => render_entry(entry)).join('')}${end}`)
    parent.replaceChildren(res)
    MathJax.typeset([parent])
    new Mark(parent).mark(query)
  }
}

function render_results_shortlist(parent, data, query) {
  if (!data) parent.replaceChildren([])
  else if (data.length === 0) parent.replaceChildren(parse_elem('<p>No results</p>'))
  else {
    const end = data.length > NUM_MAX_SIDE_RESULTS ? '<li>...</li>' : ''
    const res = parse_elem(`
      <ul>${data.slice(0, NUM_MAX_SIDE_RESULTS).map(item => `
        <li>
          <a href="${item.link}">${item.name}</a>
        </li>`).join('')}
        ${end}
      </ul>`)
    parent.replaceChildren(res)
    new Mark(parent).mark(query)
  }
}


/* setup */

const init_search = async () => {
  const input = document.getElementById(ID_SEARCH_INPUT)
  const button = document.getElementById(ID_SEARCH_BUTTON)
  const entries_res = document.getElementById(ID_RESULTS_ENTRIES)
  const authors_res = document.getElementById(ID_RESULTS_AUTHORS)
  const topics_res = document.getElementById(ID_RESULTS_TOPICS)

  const search_query = get_query('s')
  if (search_query) input.value = search_query.replace('+', ' ')

  const index_data = await Promise.all([
    fetch('/entries/index.json'),
    fetch('/authors/index.json'),
    fetch('/topics/index.json'),
    fetch('/data/keywords.json')
  ])
  const index_json = await Promise.all(index_data.map(r => r.json()))
  const indexes = build_indexes(...index_json)

  const run_local_search = (query) => {
    let res = {}
    if (query && query.length > 1) {
      add_suggestions(indexes['suggest'], query)
      res = local_search(indexes, query)
    }
    render_results_shortlist(authors_res, res.authors, query)
    render_results_shortlist(topics_res, res.topics, query)
    render_entries_results(entries_res, res.entries, query)
  }

  const handle_submit = (query) => {
    if (typeof history.pushState !== 'undefined') {
      history.pushState({}, 'Search the Archive - ' + query, '?s=' + query)
    }
    run_local_search(query)
  }

  input.addEventListener('keydown', (event) => {
    switch (event.key) {
      case 'Enter':
        event.preventDefault()
        handle_submit(event.target.value)
    }
  })

  input.addEventListener('input', () => run_local_search(input.value))
  button.addEventListener('click', () => handle_submit(input.value))

  if (input.value) run_local_search(input.value)
  input.focus()
}

document.addEventListener('DOMContentLoaded', init_search)
