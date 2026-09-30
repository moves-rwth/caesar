const RELEASES_URL = 'https://github.com/moves-rwth/caesar/releases';
const RELEASE_API_URL = 'https://api.github.com/repos/moves-rwth/caesar/releases/latest';

function selectLatestPost(blogPosts = []) {
  const posts = blogPosts
    .map(({metadata}) => metadata)
    .filter(({unlisted, frontMatter}) => !unlisted && !frontMatter?.unlisted && !frontMatter?.draft)
    .sort((a, b) => new Date(b.date) - new Date(a.date));
  const latest = posts[0];
  if (!latest) {
    return null;
  }
  const {title, date, permalink, description} = latest;
  return {title, date: new Date(date).toISOString(), permalink, description};
}

async function fetchLatestRelease() {
  const token = process.env.GITHUB_TOKEN;
  try {
    const response = await fetch(RELEASE_API_URL, {
      headers: {
        Accept: 'application/vnd.github+json',
        'User-Agent': 'caesar-website',
        'X-GitHub-Api-Version': '2022-11-28',
        ...(token ? {Authorization: `Bearer ${token}`} : {}),
      },
      signal: AbortSignal.timeout(5000),
    });
    if (!response.ok) {
      throw new Error('Release request failed');
    }
    const release = await response.json();
    if (
      !release ||
      release.draft !== false ||
      release.prerelease !== false ||
      !release.published_at ||
      typeof release.tag_name !== 'string' ||
      !release.tag_name.trim()
    ) {
      throw new Error('No published stable release');
    }
    return {
      label: `Caesar ${release.tag_name}`,
      url: `${RELEASES_URL}/tag/${encodeURIComponent(release.tag_name)}`,
    };
  } catch {
    console.warn('[homepage-metadata] Could not retrieve the latest release; using the releases link.');
    return {label: 'Latest release', url: `${RELEASES_URL}/latest`};
  }
}

module.exports = function homepageMetadata() {
  return {
    name: 'homepage-metadata',
    configureWebpack() {
      return {
        module: {
          rules: [{test: /\.heyvl$/, resourceQuery: /raw/, type: 'asset/source'}],
        },
      };
    },
    loadContent() {
      return fetchLatestRelease();
    },
    allContentLoaded({allContent, actions}) {
      const blog = allContent['docusaurus-plugin-content-blog']?.default;
      actions.setGlobalData({
        latestPost: selectLatestPost(blog?.blogPosts),
        latestRelease: allContent['homepage-metadata'].default,
      });
    },
  };
};
