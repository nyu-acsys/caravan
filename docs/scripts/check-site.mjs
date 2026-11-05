import assert from 'node:assert/strict'
import { existsSync, readFileSync, readdirSync } from 'node:fs'
import { join } from 'node:path'
import { siteBase } from '@nyu-acsys/docs-kit/config'
import project from '../.vitepress/project.mjs'

const root = project.root
const output = join(root, '.vitepress/dist')
const base = siteBase(project)
const origin = 'https://site.example.invalid'

function pages(directory) {
  return readdirSync(directory, { withFileTypes: true }).flatMap(entry => {
    const path = join(directory, entry.name)
    return entry.isDirectory() ? pages(path) : entry.name.endsWith('.html') ? [path] : []
  })
}

const htmlPages = pages(output)
for (const file of htmlPages) {
  const html = readFileSync(file, 'utf8')
  const path = file.slice(output.length + 1).replaceAll('\\', '/')
  const page = new URL(base + path.replace(/index\.html$/, ''), origin)
  for (const match of html.matchAll(/\b(?:href|src)="([^"]+)"/g)) {
    const url = new URL(match[1].replaceAll('&amp;', '&'), page)
    if (url.origin !== origin) continue
    assert.ok(url.pathname.startsWith(base), `Link escapes the deployment base: ${url.href}`)
    const relative = decodeURIComponent(url.pathname.slice(base.length))
    let target = join(output, relative)
    if (url.pathname.endsWith('/')) target = join(target, 'index.html')
    else if (!existsSync(target) && existsSync(`${target}.html`)) target += '.html'
    assert.ok(existsSync(target), `Broken link in ${path}: ${match[1]}`)
    if (url.hash && target.endsWith('.html')) {
      const anchor = decodeURIComponent(url.hash.slice(1))
      assert.ok(readFileSync(target, 'utf8').includes(`id="${anchor}"`), `Missing anchor in ${path}: ${match[1]}`)
    }
  }
}
assert.equal(existsSync(join(output, 'README.html')), false)
assert.equal(existsSync(join(output, '.site-kit')), false)
assert.equal(existsSync(join(output, 'test')), false)
const example = join('examples', 'negate.ml')
assert.deepEqual(readFileSync(join(output, example)), readFileSync(join(root, example)))
const guideSource = readFileSync(join(root, 'getting-started/index.md'), 'utf8')
const snippet = guideSource.match(/```caravan\n([\s\S]*?)\n```/)
assert.equal(snippet?.[1], readFileSync(join(root, example), 'utf8').trimEnd(), 'The displayed example must match the verified source')
for (const logo of ['logo.png', 'logo-small.png']) {
  assert.deepEqual(readFileSync(join(output, logo)), readFileSync(join(root, '../.github/assets', logo)))
}
const guide = readFileSync(join(output, 'getting-started/index.html'), 'utf8')
assert.ok(guide.includes('language-caravan'), 'The example must use Caravan syntax highlighting')
assert.ok(/<span[^>]*>\s*ensures\s*<\/span>/.test(guide), 'Annotation keywords must be highlighted')
console.log(`site-check: ${htmlPages.length} pages, links, anchors, branding and example download verified (${base})`)
