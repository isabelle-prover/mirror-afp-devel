/* constants */

const URL_FINDFACTS = 'https://search.isabelle.in.tum.de'

const NUM_MAX_SIDE_RESULTS = 4
const NUM_MAX_MAIN_RESULTS = 15

const ID_SEARCH_INPUT = 'search-input'
const ID_SEARCH_BUTTON = 'search-button'
const ID_RESULTS_ENTRIES = 'search-results'
const ID_RESULTS_AUTHORS = 'author-results'
const ID_RESULTS_TOPICS = 'topic-results'
const ID_RESULTS_FINDFACTS = 'find-facts-results'


/* index */

function build_indexes(entries, authors, topics, keywords) {
  const entry_index = new FlexSearch.Document({
    encoder: 'advanced',
    tokenize: 'forward',
    document: {
      id: 'id',
      index: ['shortname', 'title', 'abstract', 'date', 'topics[]', 'authors[]'],
      store: true,
    },
  })
  entries.forEach(entry => entry_index.add(entry))

  const author_index = new FlexSearch.Document({
    encoder: 'advanced',
    tokenize: 'forward',
    document: {
      id: 'id',
      index: 'name',
      store: true
    },
  })
  authors.forEach(author => author_index.add(author))

  const topic_index = new FlexSearch.Document({
    encoder: 'icase',
    tokenize: 'forward',
    document: {
      id: 'id',
      index: 'name',
      store: true
    },
  })
  topics.forEach(topic => topic_index.add(topic))

  const suggest_index = get_suggest_index(keywords)

  return {
    entry: entry_index,
    author: author_index,
    topic: topic_index,
    suggest: suggest_index,
  }
}

async function get_findfacts_index() {
  const indexes = await fetch(URL_FINDFACTS + '/v1/indexes').then(async http_res => {
    if (http_res.status !== 200) {
      console.log(`Error ${http_res.status} when fetching indexes: ${http_res.statusText}`)
      return Promise.resolve([])
    }
    return await http_res.json()
  }).catch((err) => {
    console.log(`Could not fetch indexes: ${err}`)
    return Promise.resolve([])
  })

  return indexes.find(index => index.startsWith('default_'))
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

async function findfacts_search(index, query) {
  if (!index) return {}
  const facet_query = {
    filters: [
      {
        field: 'SourceCode',
        filter: {
          Term: {
            inner: query
          }
        }
      }
    ],
    fields: ['Kind'],
    maxFacets: 5
  }
  const facet = await fetch(`${URL_FINDFACTS}/v1/${index}/facet`, {
      method: 'POST',
      mode: 'cors',
      headers: {
        'Content-Type': 'application/json',
      },
      body: JSON.stringify(facet_query),
    }
  ).then(async (response) => {
    if (response.status !== 200) {
      console.log(`Error ${http_res.status} on findfacts query: ${http_res.statusText}`)
      return {}
    } else {
      const json = await response.json()
      return json['Kind']
    }
  }).catch((err) => {
    console.log(`Error in findfacts query: ${err}`)
    return {}
  })
  const search_query = `{"term"%3A"${encodeURIComponent(query)}"}`
  const url = `${URL_FINDFACTS}/#search/${index}?q=${search_query}`

  return {facet: facet, url: url}
}


/* result handling */

function render_entry(entry) {
  const authors = entry.authors.join(', ')
  const topics = entry.topics.map((topic, key) =>
    `<a href=/topics/${entry.topic_links[key]}>${topic}</a>`).join(', ')
  const year = entry.date.substring(0, 4)

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

function render_entries_results(data, query) {
  if (!data) return parse_elem('<p>Please enter a search term above.</p>')
  if (data.length === 0) return parse_elem('<p>No results.</p>')
  else {
    const end = data.length > NUM_MAX_MAIN_RESULTS ? '...' : ''
    const res = parse_elem(`
      ${data.slice(0, NUM_MAX_MAIN_RESULTS).map(entry => render_entry(entry)).join('')}${end}`)
    new Mark(res).mark(query)
    return res
  }
}

function render_results_shortlist(data, query) {
  if (!data) return ''
  if (data.length === 0) return parse_elem('<p>No results</p>')
  else {
    const end = data.length > NUM_MAX_SIDE_RESULTS ? '<li>...</li>' : ''
    const res = parse_elem(`
      <ul>${data.slice(0, NUM_MAX_SIDE_RESULTS).map(item => `
        <li>
          <a href="${item.link}">${item.name}</a>
        </li>`).join('')}
        ${end}
      </ul>`)
    new Mark(res).mark(query)
    return res
  }
}

function render_findfacts_results(res) {
  if (res.facet && Object.keys(res.facet).length > 0) {
    return parse_elem(`
      <ul>${(Object.entries(res.facet).map(([name, count]) => `
        <li>
          <a href="${escape_html(res.url)}" target="_blank" rel="noreferrer noopener">
            ${count} ${name}s
          </a>
        </li>`).join(''))}
      </ul>`)
  } else return parse_elem('<p>No results</p>')
}


/* input handling */

function debounce(callback, wait) {
  let timeout
  return (...args) => {
    clearTimeout(timeout)
    timeout = setTimeout(function () {
      callback.apply(this, args)
    }, wait)
  }
}

function handleSubmit(value) {
  if (typeof history.pushState !== 'undefined') {
    history.pushState({}, 'Search the Archive - ' + value, '?s=' + value)
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
    fetch('/index.json'),
    fetch('/authors/index.json'),
    fetch('/topics/index.json'),
    fetch('/data/keywords.json')
  ])
  const index_json = await Promise.all(index_data.map(r => r.json()))
  const indexes = build_indexes(...index_json)

  input.addEventListener('keydown', (event) => {
    switch (event.key) {
      case 'Enter':
        event.preventDefault()
        handleSubmit(event.target.value)
    }
  })

  const run_local_search = (query) => {
    let res = {}
    if (query && query.length > 1) {
      add_suggestions(indexes['suggest'], query)
      res = local_search(indexes, query)
    }
    authors_res.replaceChildren(render_results_shortlist(res.authors, query))
    topics_res.replaceChildren(render_results_shortlist(res.topics, query))
    entries_res.replaceChildren(render_entries_results(res.entries, query))
    MathJax.typeset()
  }

  input.addEventListener('keyup', (event) => {
    switch (event.key) {
      case 'Enter':
      case 'Up':
      case 'ArrowUp':
      case 'Down':
      case 'ArrowDown':
      case 'Left':
      case 'ArrowLeft':
      case 'Right':
      case 'ArrowRight':
      case 'Escape':
        break
      default:
        run_local_search(event.target.value)
    }
  })
  button.addEventListener('click', () => handleSubmit(input.value))

  if (input.value) run_local_search(input.value)
  input.focus()

  // findfacts
  const findfacts_res = document.getElementById(ID_RESULTS_FINDFACTS)
  const findfacts_index = await get_findfacts_index()
  const memoized_findfacts_search = memoize(findfacts_search)

  const run_findfacts_search = async (query) => {
    let res = {}
    if (query && query.length > 2) {
      findfacts_res.replaceChildren(parse_elem('<p>...</p>'))
      res = await memoized_findfacts_search([findfacts_index, query])
    }
    findfacts_res.replaceChildren(render_findfacts_results(res))
  }

  input.addEventListener('keyup', debounce(async (event) =>
    run_findfacts_search(event.target.value), 300))

  if (input.value) await run_findfacts_search(input.value)
}

document.addEventListener('DOMContentLoaded', init_search)
