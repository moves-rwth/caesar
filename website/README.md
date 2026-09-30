# Website

This website is built using [Docusaurus 3](https://docusaurus.io/).
Use Node.js 22.12 or newer (Node.js 24 is used in CI) and Yarn Classic 1.22.

### Installation

```
$ yarn install --frozen-lockfile
```

### Local Development

```
$ yarn start
```

This command starts a local development server and opens up a browser window.
Most changes are reflected live without having to restart the server.

### Build

```
$ yarn build
```

This command generates static content into the `build` directory and can be served using any static contents hosting service.

### Social Previews

The website uses `static/img/social-card-v2.png` (1200 × 630) as its default sharing image.
The matching GitHub export is `static/img/social-card-github.png` (1280 × 640).
Both have editable, self-contained SVG sources alongside them, using Helvetica, Menlo, and STIX Two Math with fallback fonts.
Keep the code excerpt aligned with the homepage example in `static/examples/geometric-runtime.heyvl` and the colors aligned with the homepage styles.

To regenerate the PNGs with [librsvg](https://gnome.pages.gitlab.gnome.org/librsvg/), run these commands from `website` with those fonts installed:

```sh
rsvg-convert -o static/img/social-card-v2.png static/img/social-card-v2.svg
rsvg-convert -o static/img/social-card-github.png static/img/social-card-github.svg
```

Check the exports at full size and thumbnail size after editing.
Keep the GitHub PNG below 1 MB and upload it separately under the repository's **Settings → General → Social preview**.
Deploying the website does not update the repository's preview image.
The default image dimensions and alternative text live in `docusaurus.config.js`; update them together with the image, and override them if a page introduces different artwork.

### Deployment

Using SSH:

```
$ USE_SSH=true yarn deploy
```

Not using SSH:

```
$ GIT_USER=<Your GitHub username> yarn deploy
```

If you are using GitHub pages for hosting, this command is a convenient way to build the website and push to the `gh-pages` branch.
