import { defineProjectSite, siteBase } from '@nyu-acsys/docs-kit/config'
import project from './project.mjs'

const base = siteBase(project)

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
      { text: 'Get started', link: '/getting-started/' },
      { text: 'Examples', link: 'https://github.com/nyu-acsys/caravan/tree/main/test/saturn' },
      { text: 'Raven', link: 'https://nyu-acsys.github.io/raven/' }
    ],
    socialLinks: [
      { icon: 'github', link: 'https://github.com/nyu-acsys/caravan' }
    ],
    footer: {
      message: 'Released under the <a href="https://github.com/nyu-acsys/caravan/blob/main/LICENSE">MIT License</a>.',
      copyright: 'The ACSys group at New York University'
    }
  }
})
