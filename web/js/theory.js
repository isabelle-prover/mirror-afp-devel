/* constants */

const BROWSER_INFO = '/browser_info/current/'
const CLASS_LOADER = 'loader'
const CLASS_ANIMATION = 'animation'
const ID_THEORY = 'theory'


/* redirect hrefs */

function target(base, href) {
  const url = new URL(href, base)
  const is_not_theory =
    !url.pathname.startsWith(BROWSER_INFO) ||
    strip_prefix(url.pathname, BROWSER_INFO).split('/').length > 3

  if (is_not_theory) return url.href
  else return href
}


/* theory lazy-loading */

async function fetch_theory(href) {
  const html_str = await fetch(href).then((http_res) => {
    if (http_res.status !== 200)
      return Promise.resolve(
        `<body><pre>Could not load theory: ${http_res.statusText}</pre></body>`)
    else return http_res.text()
  }).catch((_) => {
    console.log(`Could not load theory at '${href}'. Redirecting...`)
    window.location.replace(href)
  })

  const parser = new DOMParser()
  const html = parser.parseFromString(html_str, 'text/html')
  return html.getElementsByTagName('body')[0]
}

const load_theory = async () => {
  const thy_elem = document.getElementById(ID_THEORY)

  if (thy_elem) {
    const thy_href = thy_elem.getAttribute("href")
    const spinner =
      parse_elem(
        `<div id="spinner" class=${CLASS_LOADER}><div class=${CLASS_ANIMATION}></div></div>`)
    thy_elem.replaceWith(spinner)

    const thy_body = await fetch_theory(thy_href)
    for (const link of thy_body.getElementsByTagName('a')) {
      const rel_href = link.getAttribute('href')
      link.setAttribute('href', target(thy_href, rel_href))
    }

    const thy_pre = Array(...thy_body.getElementsByTagName("pre"))[0]
    document.getElementById("spinner").replaceWith(thy_pre)
  }
}

document.addEventListener('DOMContentLoaded', load_theory)
