// @ts-check
// Note: type annotations allow type checking and IDEs autocompletion

import {themes as prismThemes} from 'prism-react-renderer';
import remarkMath from 'remark-math';
import rehypeKatex from 'rehype-katex';

/** @type {import('@docusaurus/types').Config} */
const config = {
  title: 'Caesar',
  tagline: 'Verify probabilistic programs with Caesar, a deductive verifier built on the HeyVL intermediate verification language.',
  favicon: 'img/laurel-square.svg',

  // Set the production url of your site here
  url: 'https://www.caesarverifier.org',
  // Set the /<baseUrl>/ pathname under which your site is served
  // For GitHub pages deployment, it is often '/<projectName>/'
  baseUrl: '/',

  // GitHub pages deployment config.
  // If you aren't using GitHub pages, you don't need these.
  organizationName: 'moves-rwth', // Usually your GitHub org/user name.
  projectName: 'caesar', // Usually your repo name.

  // the broken links detection seems to be broken for links to images in the blog, so we set it to warn only
  onBrokenLinks: 'warn',
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
          editUrl:
            'https://github.com/moves-rwth/caesar/tree/main/website/',
          remarkPlugins: [remarkMath],
          rehypePlugins: [rehypeKatex],
        },
        blog: {
          blogSidebarCount: 20,
          showReadingTime: true,
          editUrl:
            'https://github.com/moves-rwth/caesar/tree/main/website/',
          remarkPlugins: [remarkMath],
          rehypePlugins: [rehypeKatex],
        },
        theme: {
          customCss: require.resolve('./src/css/custom.css'),
        },
        gtag: {
          trackingID: 'G-73RDXJSM5X',
          anonymizeIP: true,
        },
      }),
    ],
  ],

  stylesheets: [
    {
      href: 'https://cdn.jsdelivr.net/npm/katex@0.13.24/dist/katex.min.css',
      type: 'text/css',
      integrity:
        'sha384-odtC+0UGzzFL/6PNoE8rX/SPcQDXBJ+uRepguP4QkPCm2LBxH3FA3y+fKSiJ+AmM',
      crossorigin: 'anonymous',
    },
  ],

  themeConfig:
    /** @type {import('@docusaurus/preset-classic').ThemeConfig} */
    ({
      // Replace with your project's social card
      image: 'img/social-card.png',
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
            to: '/about',
            position: 'left',
            label: 'About',
          },
          {to: '/blog', label: 'News', position: 'left'},
          {
            href: 'https://github.com/moves-rwth/caesar',
            label: 'GitHub',
            position: 'right',
          },
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
                label: 'Proof Rules',
                to: '/docs/proof-rules',
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
                label: 'About',
                to: '/about',
              },
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
        theme: prismThemes.nightOwlLight,
        darkTheme: prismThemes.nightOwl,
        additionalLanguages: ['bash', 'shell-session'],
      },
      algolia: {
        appId: 'Q93W1TPDIE',
        apiKey: '8dc15a6ca0d7a01e9f7ab673468d63a1',
        indexName: 'caesarverifier',
      }
    }),
};

module.exports = config;
