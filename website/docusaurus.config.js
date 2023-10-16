// @ts-check
// Note: type annotations allow type checking and IDEs autocompletion

const lightCodeTheme = require('prism-react-renderer/themes/nightOwlLight');
const darkCodeTheme = require('prism-react-renderer/themes/nightOwl');

/** @type {import('@docusaurus/types').Config} */
const config = {
  title: 'Caesar',
  tagline: 'A Deductive Verifier for Probabilistic Programs',
  favicon: 'img/laurel.svg',

  // Set the production url of your site here
  url: 'https://www.caesarverifier.org',
  // Set the /<baseUrl>/ pathname under which your site is served
  // For GitHub pages deployment, it is often '/<projectName>/'
  baseUrl: '/',

  // GitHub pages deployment config.
  // If you aren't using GitHub pages, you don't need these.
  organizationName: 'moves-rwth', // Usually your GitHub org/user name.
  projectName: 'caesar', // Usually your repo name.

  onBrokenLinks: 'throw',
  onBrokenMarkdownLinks: 'warn',

  // Even if you don't use internalization, you can use this field to set useful
  // metadata like html lang. For example, if your site is Chinese, you may want
  // to replace "en" with "zh-Hans".
  i18n: {
    defaultLocale: 'en',
    locales: ['en'],
  },

  markdown: {
    mermaid: true,
  },
  themes: ['@docusaurus/theme-mermaid'],

  presets: [
    [
      'classic',
      /** @type {import('@docusaurus/preset-classic').Options} */
      ({
        docs: {
          sidebarPath: require.resolve('./sidebars.js'),
          // Please change this to your repo.
          // Remove this to remove the "edit this page" links.
          editUrl:
            'https://github.com/moves-rwth/caesar/tree/main/website/',
        },
        blog: {
          showReadingTime: true,
          // Please change this to your repo.
          // Remove this to remove the "edit this page" links.
          editUrl:
            'https://github.com/moves-rwth/caesar/tree/main/website/',
        },
        theme: {
          customCss: require.resolve('./src/css/custom.css'),
        },
      }),
    ],
  ],

  themeConfig:
    /** @type {import('@docusaurus/preset-classic').ThemeConfig} */
    ({
      // Replace with your project's social card
      image: 'img/architecture-oopsla23.svg',
      navbar: {
        title: 'Caesar',
        logo: {
          alt: 'Caesar Logo',
          src: 'img/laurel.svg',
        },
        items: [
          {to: '/docs/getting-started', label: 'Getting Started', position: 'left'},
          {
            type: 'docSidebar',
            sidebarId: 'docsSidebar',
            position: 'left',
            label: 'Docs',
          },
          {
            href: 'https://github.com/moves-rwth/caesar',
            label: 'GitHub',
            position: 'right',
          },
          {to: '/blog', label: 'News', position: 'left'},
          {to: '/docs/publications', label: 'Publications', position: 'right'},
        ],
      },
      footer: {
        style: 'dark',
        links: [
          {
            title: 'Documentation',
            items: [
              {
                label: 'Getting Started',
                to: '/docs/getting-started',
              },
              {
                label: 'HeyVL',
                to: '/docs/heyvl',
              },
              {
                label: 'Standard Library',
                to: '/docs/stdlib',
              },
              {
                label: 'pGCL',
                to: '/docs/pgcl',
              },
            ],
          },
          {
            title: 'Community',
            items: [
              {
                label: 'Caesar Discussions',
                href: 'https://github.com/moves-rwth/caesar/discussions',
              },
              {
                label: 'Academic Publications',
                href: '/docs/publications',
              },
            ],
          },
          {
            title: 'More',
            items: [
              {
                label: 'News',
                to: '/blog',
              },
              {
                label: 'GitHub',
                href: 'https://github.com/moves-rwth/caesar',
              },
            ],
          },
        ],
        copyright: `Copyright © ${new Date().getFullYear()} Caesar Developers. Built with Docusaurus.`,
      },
      prism: {
        theme: lightCodeTheme,
        darkTheme: darkCodeTheme,
        additionalLanguages: ['bash', 'shell-session'],
      },
    }),
};

module.exports = config;
