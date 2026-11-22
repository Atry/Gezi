{ ... }: {
  # Joe Leslie-Hurd's opentheory tool, the reference reader of OpenTheory article files
  # (format version 6, https://www.gilith.com/opentheory/article.html), built from source
  # with nixpkgs' Poly/ML. It is the independent checker of the Gezi trace, which is
  # an OpenTheory article (https://github.com/Atry/private-overlay/issues/1561 D7). Surfaced via
  # modules/artifacts.nix as `nix build .#opentheory -L`, and put on the dev shell's PATH
  # by modules/opentheory-devshell.nix; gezi/tests/check_opentheory_article.sh is the
  # command tests call.
  #
  # The source is the signed tag v1.4.20230321 ("Version 1.4 (release 20230321)", the
  # latest release) of the development repository https://github.com/gilith/opentheory;
  # master is one commit ahead of it, touching only repo/robots.txt. The release tarball
  # https://www.gilith.com/software/opentheory/opentheory.tar.gz has the same Makefile and
  # the same src/ but for src/selftest.sml, and its URL names no version, so it cannot be
  # pinned. postPatch makes the three files in which the build of the development
  # repository would differ from the release's:
  # - Makefile.dev, which the Makefile includes: the development one turns the tool's
  #   debugging code on (`MLPP_OPTS += -r 'OpenTheoryDebug'`); the release has none, and
  #   the Makefile's own rule for it writes an empty one.
  # - bin/mosml/Makefile.src, which the Makefile includes: the release's is generated and
  #   holds only the rules of the Moscow ML build, so an empty one serves Poly/ML.
  # - src/selftest.sml, the self test's source: the release's is a copy of test/test.sml.
  # The release also ships test/repos/test, the package repository the self test reads;
  # the development repository builds it with the tool (`make test-repository` in
  # Makefile.dev), which preCheck repeats.
  #
  # The check phase is upstream's test suite, `make -C test polyml`: the self test and
  # scripts/tool-test, their output compared with test/result.ok. The suite installs
  # packages from a local repository through file:// URLs, so it needs curl, and the
  # tool computes package checksums with `shasum`, which perl provides. The installed tool
  # is not wrapped with them: the commands that fetch or pack packages (install, update,
  # upload) find curl, shasum and tar on the PATH, and `info` on an article needs none.
  config.perSystem = { pkgs, ... }: {
    packages.opentheory = pkgs.stdenv.mkDerivation {
      pname = "opentheory";
      version = "1.4.20230321";

      src = pkgs.fetchFromGitHub {
        owner = "gilith";
        repo = "opentheory";
        # The commit of the tag v1.4.20230321.
        rev = "4e7d25943446ff209fb627167b93567bd8c38118";
        hash = "sha256-9VTnKZi29sfBX7ermyW8O0DxegPGZnWKctGVLossQ4Q=";
      };

      nativeBuildInputs = [ pkgs.polyml pkgs.perl ];

      postPatch = ''
        patchShebangs scripts
        echo > Makefile.dev
        mkdir -p bin/mosml
        : > bin/mosml/Makefile.src
        cp test/test.sml src/selftest.sml
      '';

      buildPhase = ''
        runHook preBuild
        make bin/polyml/opentheory bin/polyml/selftest
        runHook postBuild
      '';

      doCheck = true;
      nativeCheckInputs = [ pkgs.curl ];

      preCheck = ''
        bin/polyml/opentheory -d test/repos/test init
        for theory in empty bool-true-def bool-true-thm bool-true \
            bool-true-assert bool-true-axiom; do
          bin/polyml/opentheory -d test/repos/test \
            install --manual test/theories/$theory/$theory.thy
        done
      '';

      # The test Makefile's two temporary files default to /tmp; they go to the build's
      # TMPDIR instead.
      checkPhase = ''
        runHook preCheck
        make -C test polyml \
          TMPFILE1=$TMPDIR/golden-reference TMPFILE2=$TMPDIR/test-output
        runHook postCheck
      '';

      installPhase = ''
        runHook preInstall
        install -D -m 755 bin/polyml/opentheory $out/bin/opentheory
        runHook postInstall
      '';

      meta = {
        description = "Processes higher order logic theory packages in OpenTheory format";
        homepage = "https://www.gilith.com/opentheory/";
        license = pkgs.lib.licenses.mit;
        mainProgram = "opentheory";
      };
    };
  };
}
