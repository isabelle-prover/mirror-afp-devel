/* constants */

const ID_THEORY_LIST = 'theories'
const CLASS_LOADER = 'loader'
const CLASS_ANIMATION = 'animation'
const CLASS_COLLAPSIBLE = 'collapsible'
const ATTRIBUTE_THEORY_SRC = 'theory-src'
const CLASS_NAVBAR_TYPE = 'theory-navbar-type'
const CLASS_THY_NAV = 'thy-nav'
const PARAM_NAVBAR_TYPE = 'theory-navbar-type'
const ID_NAVBAR_TYPE_SELECTOR = 'navbar-type-selector'
const ID_NAVBAR = 'theory-navbar'
const DEFAULT_NAVBAR_TYPE = 'fact'


/* routing */

function target(base_href, rel_href) {
  const href_parts = rel_href.split('/')

  if (href_parts.length === 1) return `#${href_parts[0]}`
  else if (href_parts.length === 3 && href_parts[0] === '..' && href_parts[1] !== '..') {
    return `/entries/${href_parts[1].toLowerCase()}/theories#${href_parts[2]}`
  }
  else return `${base_href}/${rel_href}`
}

function to_id(thy_name, ref) {
  if (ref) return `${thy_name}.html#${ref}`
  else return `${thy_name}.html`
}

const to_container_id = (thy_name) => `${thy_name}#container`
const to_collapsible_id = (thy_name) => `${thy_name}#collapsible`
const to_spinner_id = (thy_name) => `${thy_name}#spinner`
const to_nav_id = (thy_name) => `${thy_name}#nav`
const to_ul_id = (thy_name) => `${thy_name}#ul`
const of_ul_id = (id) => id.split('#').slice(0, -1).join('#')
const to_a_id = (thy_name) => `${thy_name}#a`

function set_query(attribute, value) {
  const params = new URLSearchParams(window.location.search)
  params.set(attribute, value)

  const fragment = window.location.hash.length > 1 ? window.location.hash: ''
  const new_url = `${window.location.origin}${window.location.pathname}?${params.toString()}${fragment}`

  if (history.pushState) window.history.pushState({path: new_url}, '', new_url)
  else window.location = new_url
}

function get_query(attribute) {
  const params = new URLSearchParams(window.location.search)
  return params.get(attribute)
}


/* document translation */

function translate(base_href, thy_name, thy_body) {
  const thy_refs = [...thy_body.getElementsByTagName('span')].map((span) => {
    let ref = span.getAttribute('id')
    if (ref) {
      span.setAttribute('id', to_id(thy_name, ref))
    }
    return ref
  }).filter(e => e)
  for (const link of thy_body.getElementsByTagName('a')) {
    const rel_href = link.getAttribute('href')
    link.setAttribute('href', target(base_href, rel_href))
  }
  return thy_refs
}


/* theory lazy-loading */

async function fetch_theory_body(href) {
  const html_str = await fetch(href).then((http_res) => {
    if (http_res.status !== 200) return Promise.resolve(`<body>${http_res.statusText}</body>`)
    else return http_res.text()
  }).catch((_) => {
    console.log(`Could not load theory at '${href}'. Redirecting...`)
    window.location.replace(href)
  })

  const parser = new DOMParser()
  const html = parser.parseFromString(html_str, 'text/html')
  return html.getElementsByTagName('body')[0]
}

async function load_theory(thy_name, href) {
  const thy_body = await fetch_theory_body(href)
  const refs = translate(href, thy_name, thy_body)

  const collapse = document.getElementById(to_collapsible_id(thy_name))
  collapse.append(...Array(...thy_body.children).slice(1))
  return refs
}

async function open_theory(thy_name) {
  const collapsible = document.getElementById(to_collapsible_id(thy_name))

  if (collapsible) open(collapsible)
  else {
    const container = document.getElementById(to_container_id(thy_name))

    if (container) {
      const collapsible = parse_elem(`
        <div id="${to_collapsible_id(thy_name)}" style="display: block">
          <div id="${to_spinner_id(thy_name)}" class=${CLASS_LOADER}><div class=${CLASS_ANIMATION}></div></div>
        </div>`)
      container.appendChild(collapsible)
      let refs = await load_theory(thy_name, container.getAttribute(ATTRIBUTE_THEORY_SRC))
      await load_theory_nav(thy_name, refs)
      const spinner = document.getElementById(to_spinner_id(thy_name))
      spinner.parentNode.removeChild(spinner)
    }
  }
}

function nav_tree_rec(thy_name, path, key, ref_parts, type) {
  const rec_ref = ref_parts.filter(e => e.length > 0)
  const id = to_id(thy_name, `${path.join('.')}.${key}|${type}`)
  let res
  if (rec_ref.length < ref_parts.length) {
    res = `<a id="${to_a_id(id)}" class="${CLASS_SPY_LINK}" href="#${id}">${key}</a>`
  } else res = `${key}`

  if (rec_ref.length > 1) {
    const by_key = group_by(rec_ref)
    const children = Object.keys(by_key).map((key1) => `
      <li>${nav_tree_rec(thy_name, [...path, key], key1, by_key[key1], type)}</li>`)
    return `
      ${res}
      <ul id="${to_ul_id(id)}" class="${CLASS_COLLAPSIBLE}" style="display: none">
        ${children.join('')}
      </ul>`
  } else return res
}

function nav_tree(thy_name, refs, type) {
  let trees = Object.entries(group_by(refs)).map(([key, parts]) =>
    `<li>${nav_tree_rec(thy_name, [thy_name], key, parts, type)}</li>`)

  return parse_elem(`
    <ul id="${to_ul_id(thy_name)}" class="${CLASS_NAVBAR_TYPE} ${CLASS_COLLAPSIBLE}" style="display: none">
      ${trees.join('')}
    </ul>`)
}


const cached_refs = {}
const load_theory_nav = (thy_name, refs) => {
  let selected = get_query(PARAM_NAVBAR_TYPE) ? get_query(PARAM_NAVBAR_TYPE) : DEFAULT_NAVBAR_TYPE

  let by_type = group_by(refs.filter(ref => ref.includes('|')).map((id) => id.split('|').reverse()))
  let type_selector = document.getElementById(ID_NAVBAR_TYPE_SELECTOR)
  let options = [...type_selector.options].map(e => e.value)

  for (let [type, elems] of Object.entries(by_type)) {
    if (!options.includes(type)) type_selector.appendChild(parse_elem(`<option value=${type}>${type}</option>`))

    let parts_by_thy = group_by(elems.map((s) => s[0].split('.')))
    if (!cached_refs[type]) cached_refs[type] = {}
    cached_refs[type][thy_name] = parts_by_thy[thy_name]
  }

  let tree = nav_tree(thy_name, cached_refs[selected][thy_name], selected)
  document.getElementById(to_nav_id(thy_name)).appendChild(tree)

  ScrollSpy.instance.refresh()
}


/* state */

let navbar_last_opened = []


/* controls */

const follow_theory_hash = async () => {
  let hash = window.location.hash

  if (hash.length > 1) {
    const id = hash.slice(1)

    const thy_name = strip_suffix(id.split('#')[0], '.html')
    await open_theory(thy_name)

    const elem = document.getElementById(id)
    if (elem) elem.scrollIntoView()
  }
}

const toggle_theory = async (thy_name) => {
  const hash = `#${to_id(thy_name)}`
  const collapsible = document.getElementById(to_collapsible_id(thy_name))
  if (collapsible) {
    if (!close(collapsible)) {
      if (window.location.hash === hash) open(collapsible)
      else window.location.hash = hash
    }
  } else window.location.hash = hash
}

const change_selector = (type) => {
  let old_type = get_query(PARAM_NAVBAR_TYPE)
  if (!old_type || old_type !== type) {
    set_query(PARAM_NAVBAR_TYPE, type)

    for (const elem of document.getElementsByClassName(CLASS_NAVBAR_TYPE)) {
      let thy_name = of_ul_id(elem.id)
      elem.replaceWith(nav_tree(thy_name, cached_refs[type][thy_name], type))
    }

    ScrollSpy.instance.refresh()
  }
}

const open_tree = (elem) => {
  if (elem.classList.contains(CLASS_COLLAPSIBLE)) {
    if (open(elem)) navbar_last_opened.push(elem)
  }
  if (elem.parentElement) open_tree(elem.parentElement)
}

const sync_navbar = (link) => {
  for (const elem of navbar_last_opened){
    close(elem)
  }

  open_tree(link.parentElement)

  link.scrollIntoView()
}


/* setup */

const init = async () => {
  const theory_list = document.getElementById(ID_THEORY_LIST)
  const navbar = document.getElementById(ID_NAVBAR)

  if (theory_list && navbar) {
    const thy_names = []

    for (const theory of theory_list.children) {
      thy_names.push(theory.id)

      const href = theory.getAttribute('href')
      const thy_name = theory.id

      const thy_collapsible = parse_elem(`
        <div id="${to_container_id(thy_name)}" theory-src="${href}">
          <h2 id="${to_id(thy_name)}" style="cursor: pointer" onclick="toggle_theory('${thy_name}')">
            ${thy_name}
          </h2>
        </div>`)
      theory.replaceWith(thy_collapsible)
    }

    const type = get_query(PARAM_NAVBAR_TYPE) ? get_query(PARAM_NAVBAR_TYPE) : DEFAULT_NAVBAR_TYPE
    navbar.appendChild(parse_elem(`
      <li>
        <select id=${ID_NAVBAR_TYPE_SELECTOR} onchange="change_selector(this.options[this.selectedIndex].value)">
          <option value=${type} selected="selected">${type}</option>
        </select>
      </li>`))
    navbar.append(...thy_names.map((thy_name) => parse_elem(`
      <li id="${to_nav_id(thy_name)}">
        <a id="${to_a_id(thy_name)}" class="${CLASS_SPY_LINK} ${CLASS_THY_NAV}" href="#${to_id(thy_name)}">
          ${thy_name}
        </a>
      </li>`)), parse_elem('<hr>'))

    window.onhashchange = follow_theory_hash
    window.addEventListener(EVENT_SPY_ACTIVATE, (e) => sync_navbar(e.relatedTarget))

    new ScrollSpy(document.body, 'theory-navbar')

    await follow_theory_hash()
  }
}

document.addEventListener('DOMContentLoaded', init)
