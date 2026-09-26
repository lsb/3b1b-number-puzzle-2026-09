# Lean proofs + multiplier finder in one image.
#
#   docker build -t ones-zeros .
#   docker run --rm ones-zeros prove            # re-check both Lean proofs
#   docker run --rm ones-zeros multiplier 7 12  # find multipliers
ARG BASE=debian:bookworm-slim
FROM ${BASE}

# Install the tools the build needs, unless the base image already has them.
RUN missing=""; \
    for tool in curl git python3 unzip; do command -v "$tool" >/dev/null || missing="$missing $tool"; done; \
    if [ -n "$missing" ]; then \
      apt-get update \
      && apt-get install -y --no-install-recommends ca-certificates $missing \
      && rm -rf /var/lib/apt/lists/*; \
    fi

WORKDIR /proof

# Lean, at the version pinned in lean-toolchain, straight from the GitHub release.
COPY lean-toolchain ./
RUN version="$(sed 's/.*:v//' lean-toolchain)" \
 && curl -sSfL -o /tmp/lean.zip "https://github.com/leanprover/lean4/releases/download/v${version}/lean-${version}-linux.zip" \
 && unzip -q /tmp/lean.zip -d /opt \
 && rm /tmp/lean.zip \
 && ln -s "/opt/lean-${version}-linux" /opt/lean
ENV PATH=/opt/lean/bin:$PATH

# Mathlib: fetch the sources, then the prebuilt cache if it is reachable. Without the
# cache, `lake build` below compiles the needed part of Mathlib from source (slow).
COPY lakefile.toml lake-manifest.json ./
RUN lake exe cache get || echo "Mathlib cache unavailable; building from source"

COPY *.lean find_multiplier.py run.sh ./
RUN lake build

ENTRYPOINT ["./run.sh"]
CMD ["prove"]
