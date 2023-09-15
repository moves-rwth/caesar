# Building the Docker image

To build the Docker image, **enter the project root directory** and then execute:

```bash
docker build -t caesar -f docker/Dockerfile .
```

You can create a multi-platform image using BuildKit.
We recommend running this on an MacOS ARM machine, since we have observed massive slowdowns when emulating ARM on x86 machines.
Our `buildkitd.toml` file will limit build parallelism to 1 build at a time to avoid out-of-memory situations.
```bash
docker buildx create --use --config docker/buildkitd.toml
docker buildx build -t caesar -f docker/Dockerfile . --platform linux/amd64,linux/arm64
```

To create a `.tar.gz` file of for the Docker image (single platform only):
```bash
docker save caesar | gzip > caesar.tar.gz
```
