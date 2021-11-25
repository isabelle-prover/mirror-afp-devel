function get_target(url, href) {
    const href_parts = href.split('/')

    if (href_parts.length === 1) {
        return '#' + href_parts[0].slice(0, -('.html'.length))
    } else if (href_parts.length === 3 && href_parts[0] === '..' && href_parts[1] !== '..') {
        return '/entries/' + href_parts[1].toLowerCase() + '/theories#' + href_parts[2].slice(0, -('.html'.length))
    } else {
        return url.split('/').slice(0, -1).join('/') + '/' + href
    }
}

function translate(url, content) {
    for (const link of content.getElementsByTagName('a')) {
        const href = link.getAttribute('href')
        let target = get_target(url, href)
        link.setAttribute('href', target)
    }
}

async function fetch_theory(href) {
    return fetch(href).then((http_res) => {
        if (http_res.status !== 200) {
            return Promise.resolve(`<body>${http_res.statusText}</body>`)
        } else {
            return http_res.text()
        }
    }).catch((_) => window.location.replace(href))
}

async function fetch_theory_body(href) {
    const html_str = await fetch_theory(href)
    const parser = new DOMParser()
    const html = parser.parseFromString(html_str, 'text/html')
    return html.getElementsByTagName('body')[0]
}

async function load_theory(thy_name, href) {
    const thy_body = await fetch_theory_body(href)
    translate(href, thy_body)
    const content = theory_content(thy_name)
    content.append(...Array(...thy_body.children).slice(1))
}

function theory_content(thy_name) {
    const elem = document.getElementById(thy_name)
    if (elem && elem.className === "thy-collapsible") {
        return elem.firstElementChild.nextElementSibling
    } else {
        return null
    }
}

function open_theory(thy_name) {
    const content = theory_content(thy_name)
    if (content) {
        if (content.style.display === 'none') {
            content.style.display = "block"
        }
    } else {
        const elem = document.getElementById(thy_name)
        if (elem && elem.className === "thy-collapsible") {
            const template = document.createElement('template')
            template.innerHTML = `<div id="content" style="display: block"></div>`
            const content = template.content
            elem.appendChild(content)
            load_theory(thy_name, elem.getAttribute('datasrc'))
        }
    }
}

const toggle_theory = function (thy_name) {
    const content = theory_content(thy_name)
    if (content && content.style.display === 'block') {
        content.style.display = 'none'
    } else {
        const hash = `#${thy_name}`
        if (window.location.hash === hash) {
            open_theory(thy_name)
        } else {
            window.location.hash = hash
        }
    }
}

const follow_theory_hash = function() {
    const hash = window.location.hash
    if (hash.length > 1) {
        open_theory(hash.substr(1))
    }
}

const init = function() {
    const theory_list = document.getElementById('html-theories')
    if (theory_list) {
        for (const theory of theory_list.children) {
            const thy_link = theory.firstElementChild

            const href = thy_link.getAttribute('href')
            const thy_name = thy_link.innerHTML

            const template = document.createElement('template')
            template.innerHTML = `
                <div id=${thy_name} class="thy-collapsible" datasrc=${href}>
                    <div class="head" style="cursor: pointer" onclick="toggle_theory('${thy_name}')">
                        <h1>${thy_name}</h1>
                    </div>
                </div>`
            theory.replaceWith(template.content)
        }
    }
    follow_theory_hash()
}

window.onload = init
window.onhashchange = follow_theory_hash
