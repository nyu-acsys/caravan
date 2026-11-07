import { defineProjectSite, siteBase } from '@nyu-acsys/docs-kit/config'
import { sectionItems } from '@nyu-acsys/docs-kit/sections'
import project, { tutorialChapters } from './project.mjs'

const base = siteBase(project)
const registry = project.sections.buildRegistry()
const sectionLabels = Object.fromEntries(
  Object.entries(registry.sections).map(([id, section]) => [id, section.title])
)
const tutorialSidebar = tutorialChapters.map(chapter => {
  const page = `/${chapter.path}${chapter.path.endsWith('/') ? '' : '.html'}`
  return {
    text: `${chapter.label}. ${chapter.title}`,
    link: `/${chapter.path}`,
    collapsed: false,
    items: sectionItems(registry, page, sectionLabels)
  }
})

export default defineProjectSite(project, {
  title: 'Caravan',
  description: 'SMT-based verification of multicore OCaml programs using concurrent separation logic.',
  srcExclude: ['.site-kit/**', 'README.md', 'test/**'],
  head: [
    ['link', { rel: 'icon', type: 'image/png', href: `${base}logo-small.png` }]
  ],
  markdown: { languages: ['ocaml'] },
  themeConfig: {
    logo: '/logo-small.png',
    nav: [
      { text: 'Tutorial', link: '/tutorial/' },
      { text: 'Examples', link: 'https://github.com/nyu-acsys/caravan/tree/main/test/saturn' },
      { text: 'Raven', link: 'https://nyu-acsys.github.io/raven/' }
    ],
    sidebar: { '/tutorial/': tutorialSidebar },
    socialLinks: [
      { icon: 'github', link: 'https://github.com/nyu-acsys/caravan' }
    ],
    footer: {
      message: 'Released under the <a href="https://github.com/nyu-acsys/caravan/blob/main/LICENSE">MIT License</a>.',
      copyright: 'The ACSys group at New York University'
    }
  }
})
