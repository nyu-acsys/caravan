# Caravan project site

The site uses VitePress and the shared package in Raven's `docs/site-kit`.
`SITE_KIT_REVISION` pins that package independently of Caravan's verifier pin.
Content, navigation, syntax grammars and palette belong to this repository.

From `docs/`, fetch the pinned package, install dependencies and start the site:

```bash
node scripts/fetch-site-kit.mjs
npm ci
npm run dev
```

To use an existing Raven checkout without network access:

```bash
node scripts/fetch-site-kit.mjs --source ../../raven
npm ci
```

The checkout must contain the pinned commit. The bootstrap reads its committed
tree, so local Raven modifications do not affect the site. A matching package is
reused; change `SITE_KIT_REVISION` to update it. A failed fetch preserves the prior
installation. Run the bootstrap before `npm ci`, since npm needs the local package
while resolving the lockfile.

After changing the pin, fetch the package and run `npm install --package-lock-only`
to record any changed package metadata before committing the new lockfile.

`npm test` checks the bootstrap and proof highlighting with the site renderer. `npm run build` builds a local-root site;
`GITHUB_PAGES=true npm run build` builds for `/caravan/`. `npm run preview` serves
the last build using the corresponding environment. No verifier, OCaml compiler,
or sibling checkout is needed to build the website after fetching its package.
Every build checks internal links, anchors, branding assets and the example
download against the generated output.

The language definitions are read from `vs-code/syntaxes`, keeping proof and
annotation categories consistent with the extension. The `caravan` code fence
combines OCaml with annotation highlighting; `proof` highlights companion proofs.
Logos are copied from `.github/assets` before builds. Generated assets, example
downloads and the shared package are ignored by Git.

The getting-started example and tutorial examples have cram tests under
`examples/` and are checked by Caravan's normal verifier regression suite. Tutorial
pages include their source files directly, so displayed code stays identical to
the checked examples. Keep the tutorial focused on Caravan syntax, OCaml coverage,
and semantic conventions; link to Raven's tutorial for the underlying logic.
The documentation build itself never runs the verifier.

`deploy-docs.yml` builds and deploys on `main` or a manual dispatch. Enable GitHub
Pages with **GitHub Actions** as the source for the repository. The pinned Raven
commit must be available on GitHub before a clean CI build can fetch it.

The tutorial includes installation and the first check. Its chapter order and labels
are declared in `.vitepress/project.mjs`; the shared section registry numbers marked
`##` headings and generates their sidebar entries. Give every tutorial subsection a
stable `{#sec:...}` ID so numbering, links, and navigation remain aligned. Chapter
headings include their chapter numbers, matching the configured labels. The site
check verifies complete subsection coverage and rendered numbers and sidebar links.
