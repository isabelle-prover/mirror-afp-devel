/**
 * Scrollspy, inspired from bootstrap. Original license:
 * --------------------------------------------------------------------------
 * Bootstrap (v5.1.3): scrollspy.js
 * Licensed under MIT (https://github.com/twbs/bootstrap/blob/main/LICENSE)
 *
 * --------------------------------------------------------------------------
 */

const EVENT_SPY_ACTIVATE = 'activate.spy'
const CLASS_ACTIVE = 'active'
const CLASS_SPY_LINK = 'spy-link'

/**
 * Class definition
 */

class ScrollSpy {
  constructor(element, target, offset = 0.5) {
    ScrollSpy.instance = this
    this._element = element

    this._offset = offset
    this._offsets = []
    this._link_ids = []
    this._active_id = null
    this._scrollHeight = 0
    this._target = target

    window.onscroll = () => this._process()

    this.refresh()
    this._process()
  }

  refresh() {
    this._clear()
    this._offsets = []
    this._link_ids = []
    this._scrollHeight = this._getScrollHeight()

    const targets = []
    for (const link of document.getElementById(this._target).getElementsByClassName(CLASS_SPY_LINK)) {
      // visible and has id
      if (link.id && !is_collapsed(link)) {
        const target_id = link.getAttribute('href').slice(1)
        const target = document.getElementById(target_id)

        if (target) {
          const targetBCR = target.getBoundingClientRect()
          if (targetBCR.width || targetBCR.height) {
            targets.push([targetBCR.top + window.pageYOffset, link.id])
          }
        }
      }
    }

    for (const item of targets.sort((a, b) => a[0] - b[0])) {
      this._offsets.push(item[0])
      this._link_ids.push(item[1])
    }
  }

  // Private
  _getScrollHeight() {
    return window.scrollHeight || Math.max(
      document.body.scrollHeight,
      document.documentElement.scrollHeight
    )
  }
  _process() {
    const scrollTop = window.pageYOffset + this._offset * window.innerHeight
    const scrollHeight = this._getScrollHeight()
    const maxScroll = this._offset * window.innerHeight + scrollHeight - window.innerHeight

    if (this._scrollHeight !== scrollHeight) {
      this.refresh()
    }

    if (scrollTop >= maxScroll) {
      const target_id = this._link_ids[this._link_ids.length - 1]

      if (this._active_id !== target_id) {
        this._activate(target_id)
      }

      return
    }

    if (this._active_id && scrollTop < this._offsets[0] && this._offsets[0] > 0) {
      this._clear()
      return
    }

    for (let i = this._offsets.length; i--;) {
      const isActiveTarget = this._active_id !== this._link_ids[i] &&
        scrollTop >= this._offsets[i] &&
        (typeof this._offsets[i + 1] === 'undefined' || scrollTop < this._offsets[i + 1])

      if (isActiveTarget) {
        this._activate(this._link_ids[i])
      }
    }
  }

  _activate(link_id) {
    this._clear()
    this._active_id = link_id

    const link = document.getElementById(link_id)
    if (link) {
      const elem = document.getElementById(link.getAttribute('href').slice(1))
      link.classList.add(CLASS_ACTIVE)
      elem.classList.add(CLASS_ACTIVE)

      const event = new Event(EVENT_SPY_ACTIVATE)
      event.relatedTarget = link
      window.dispatchEvent(event)
    }
  }

  _clear() {
    if (this._active_id) {
      const link = document.getElementById(this._active_id)
      if (link) {
        const elem = document.getElementById(link.getAttribute('href').slice(1))
        if (link.classList.contains(CLASS_ACTIVE)) link.classList.remove(CLASS_ACTIVE)
        if (elem.classList.contains(CLASS_ACTIVE)) elem.classList.remove(CLASS_ACTIVE)
      }
    }
  }

  static instance
}