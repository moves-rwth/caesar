// @ts-check
// Note: type annotations allow type checking and IDEs autocompletion

import {themes as prismThemes} from 'prism-react-renderer';
import remarkMath from 'remark-math';
import rehypeKatex from 'rehype-katex';
import {examples, groups} from './src/heyvl-examples/catalog.mjs';

/** @type {import('@docusaurus/types').Config} */
const config = {
  title: 'Caesar Verifier',
  tagline: 'Verify probabilistic programs with Caesar, a deductive verifier built on the HeyVL intermediate verification language.',
  favicon: 'favicon.ico',

  // Set the production url of your site here
  url: 'https://www.caesarverifier.org',
  // Set the /<baseUrl>/ pathname under which your site is served
  // For GitHub pages deployment, it is often '/<projectName>/'
  baseUrl: '/',

  // GitHub pages deployment config.
  // If you aren't using GitHub pages, you don't need these.
  organizationName: 'moves-rwth', // Usually your GitHub org/user name.
  projectName: 'caesar', // Usually your repo name.

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
  plugins: [
    require.resolve('./plugins/homepage-metadata'),
    require.resolve('./plugins/heyvl-examples/index.cjs'),
  ],

  presets: [
    [
      'classic',
      /** @type {import('@docusaurus/preset-classic').Options} */
      ({
        docs: {
          sidebarPath: require.resolve('./sidebars.js'),
          sidebarItemsGenerator: async ({defaultSidebarItemsGenerator, ...args}) => {
            const exampleId = 'getting-started/zoo';
            const detailDocs = args.docs.filter((doc) => doc.id.startsWith(`${exampleId}/`));
            const detailDocIds = new Set(detailDocs.map((doc) => doc.id));
            const exampleGroups = groups.map((group) => ({
              type: 'category',
              label: group.label,
              collapsible: true,
              collapsed: true,
              items: examples
                .filter((example) => example.group === group.id && example.detailSlug && detailDocIds.has(`${exampleId}/${example.detailSlug}`))
                .map((example) => ({type: 'doc', id: `${exampleId}/${example.detailSlug}`})),
            })).filter((group) => group.items.length);
            const items = await defaultSidebarItemsGenerator({
              ...args,
              docs: args.docs.filter((doc) => !doc.id.startsWith(`${exampleId}/`)),
            });
            function addExampleHierarchy(sidebarItems) {
              return sidebarItems.map((item) => {
                if (item.type === 'doc' && item.id === exampleId) {
                  return {
                    type: 'category',
                    label: 'HeyVL Examples',
                    link: {type: 'doc', id: exampleId},
                    collapsible: true,
                    collapsed: true,
                    className: 'example-sidebar-group',
                    items: exampleGroups,
                  };
                }
                return item.type === 'category'
                  ? {...item, items: addExampleHierarchy(item.items)}
                  : item;
              });
            }
            return addExampleHierarchy(items);
          },
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
          customCss: [
            require.resolve('katex/dist/katex.min.css'),
            require.resolve('./src/css/custom.css'),
          ],
        },
        gtag: {
          trackingID: 'G-73RDXJSM5X',
          anonymizeIP: true,
        },
      }),
    ],
  ],

  headTags: [
    {
      tagName: 'link',
      attributes: {
        rel: 'icon',
        type: 'image/png',
        sizes: '48x48',
        href: '/favicon-48x48.png',
      },
    },
    {
      tagName: 'link',
      attributes: {
        rel: 'icon',
        type: 'image/png',
        sizes: '32x32',
        href: '/favicon-32x32.png',
      },
    },
    {
      tagName: 'link',
      attributes: {
        rel: 'icon',
        type: 'image/png',
        sizes: '16x16',
        href: '/favicon-16x16.png',
      },
    },
    {
      tagName: 'link',
      attributes: {
        rel: 'icon',
        type: 'image/svg+xml',
        href: '/img/laurel-square.svg',
      },
    },
    {
      tagName: 'link',
      attributes: {
        rel: 'apple-touch-icon',
        sizes: '180x180',
        href: '/apple-touch-icon.png',
      },
    },
    {
      tagName: 'meta',
      attributes: {
        name: 'theme-color',
        content: '#146c59',
      },
    },
  ],

  themeConfig:
    /** @type {import('@docusaurus/preset-classic').ThemeConfig} */
    ({
      image: 'img/social-card-v2.png',
      mermaid: {
        options: {
          xyChart: {
            width: 340,
            height: 220,
            xAxis: {labelFontSize: 14, titleFontSize: 14},
            yAxis: {labelFontSize: 14, titleFontSize: 14},
          },
          themeVariables: {
            xyChart: {
              backgroundColor: 'transparent',
              plotColorPalette: 'var(--ifm-color-primary)',
              xAxisLabelColor: 'var(--ifm-font-color-base)',
              xAxisTitleColor: 'var(--ifm-font-color-base)',
              xAxisTickColor: 'var(--ifm-color-emphasis-600)',
              xAxisLineColor: 'var(--ifm-color-emphasis-600)',
              yAxisLabelColor: 'var(--ifm-font-color-base)',
              yAxisTitleColor: 'var(--ifm-font-color-base)',
              yAxisTickColor: 'var(--ifm-color-emphasis-600)',
              yAxisLineColor: 'var(--ifm-color-emphasis-600)',
            },
          },
        },
      },
      metadata: [
        {property: 'og:image:width', content: '1200'},
        {property: 'og:image:height', content: '630'},
        {property: 'og:image:type', content: 'image/png'},
        {
          property: 'og:image:alt',
          content: 'Caesar, verification infrastructure for probabilistic programs, beside a coin-flip loop and the verified bound 𝔼[iterations] ≤ 2.',
        },
        {
          name: 'twitter:image:alt',
          content: 'Caesar, verification infrastructure for probabilistic programs, beside a coin-flip loop and the verified bound 𝔼[iterations] ≤ 2.',
        },
      ],
      navbar: {
        title: 'Caesar',
        logo: {
          alt: 'Caesar Logo',
          src: 'img/laurel.svg',
        },
        items: [
          {to: '/docs/getting-started', label: 'Getting Started', position: 'left'},
          {to: '/docs/getting-started/zoo', label: 'Examples', position: 'left'},
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
                label: 'Cite and Share',
                to: '/about#cite-and-share',
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
