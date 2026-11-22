{ inputs, self, ... }: {
  # OCI images of Jupyter with Gezi's kernel of lambdalattice cells built in
  # (gezi/README.md, "Getting started"; the user, 2026-11-19: "我觉得不如把镜像叫做
  # lambdalattice-jupyter，而不是 lambdalattice-jupyter-console。这样的话 console 只是子命令之一，
  # 还可以用别的子命令，包括notebook"; "实际上应该叫 `gezi-jupyter`"; "可以理解为内置了gezi kernel的
  # jupyter"). The entrypoint is `jupyter`, the default command its subcommand `console`,
  # and `notebook`, `run` and the others are the arguments of `docker run`; the
  # kernel the subcommands start unless told otherwise is lambdalattice's
  # (`jupyterConfiguration` below). Imported by gezi/flake.nix and by
  # the monorepo's modules/artifacts.nix, so that `nix build -L .#<name>` builds the same
  # derivation from either; nothing here depends on which flake imports it.
  #
  # The kernel runs the data entry of the directory /gezi/entry, read by the
  # framework's generic entry; there is no default entry (the user, 2026-11-13: "Presets
  # are not 'default'. All presets should be opt-in"; "Let's create multiple images with
  # different tags then. A base image without entry.lambdalattice so that users can mount
  # and other images with different entries."). So there are:
  # - `gezi-jupyter-base`, the image `gezi-jupyter-base:latest`,
  #   whose /gezi/entry is empty, for a directory holding an entry.lambdalattice
  #   mounted there;
  # - `gezi-jupyter-<player>`, the image
  #   `gezi-jupyter:<player>`, for each in-tree entry written as data
  #   (contest-entries-<player>/entry.lambdalattice), whose entry.lambdalattice it holds at
  #   /gezi/entry. That name has no `latest` tag, so that a bare
  #   `docker run gezi-jupyter` finds no image instead of choosing an
  #   entry.
  #
  # Everything in the images is a Nix derivation: the JVM, Python, jupyter_console and
  # notebook from nixpkgs, and the kernel's jars, built by sbt inside the derivation
  # `lambdalattice-jupyter-kernel` below. The dev shell is not involved: there sbt
  # resolves its own dependencies (modules/scala-devshell.nix), while these flake packages
  # are built from reproducible derivations only, the split the LaTeX setup has between
  # modules/paper-devshell.nix and the subrepos' texlive.nix packages (the user,
  # 2026-11-13: "I think the idea is that dev shell does not use nix to manage Scala
  # packages, while the flake packages must use reproducible nix derivations, similar to
  # how we do LaTeX setup.").
  #
  # The images are devenv containers of one job of nix-ml-ops
  # (dev/nix-ml-ops/flake-modules/jobs.nix), built by nix2container: the job's devenv
  # shell carries the packages and the environment, the base is its container
  # `processes`, the container nix-ml-ops's kubernetes module pushes, and each entry's
  # image is a container of its own. devenv's containers have no base image to build on,
  # so the images share layers instead: each puts the shell's whole closure in a first
  # layer of the same store paths, which nix2container builds once and every image holds
  # by the same digest, and the tree of /gezi in a layer of its own.
  imports = [ inputs.nix-ml-ops.flakeModules.jobs ];

  config.perSystem = { pkgs, lib, config, ... }:
    let
      jdk = pkgs.jdk25_headless;

      # The directory whose entry.lambdalattice the kernel runs, inside the images.
      entryDirectory = "/gezi/entry";

      # The sbt build of Gezi, through zaninime/sbt-derivation's mkSbtDerivation,
      # the ecosystem's tool for building sbt projects in Nix (the user, 2026-11-13: "I
      # think it should adopt the existing solution in the ecosystem, instead of a home
      # made one. If the existing solution internally use batch mode, it is not a
      # violation."). It fetches sbt's dependencies in a fixed-output derivation, whose
      # hash is `depsSha256` below, and builds offline from them. The sbt of nixpkgs is
      # sbt 2's runner, under which plain `sbt` is the thin client that starts a server in
      # the background; the commands below say `--client` and end with `shutdown`, so that
      # no server is left writing to the caches the fixed-output derivation packs.
      #
      # When a dependency of the build changes (a library, a plugin, sbt's or Scala's
      # version), the fixed-output derivation's hash changes: set `depsSha256` to
      # `lib.fakeHash`, build `.#lambdalattice-jupyter-kernel`, and copy the hash Nix
      # reports as `got:`.
      #
      # The task the derivation runs is the build's own installer,
      # `jupyter-kernel/jupyterKernelInstall` (gezi/jupyter-kernel/build.sbt), given
      # the images' entry directory: a coursier launcher holding the kernel's whole class
      # path, and almond's kernel.json, whose paths of the launcher name the build's
      # directory; installPhase moves both into $out and rewrites those paths.
      kernel = inputs.sbt-derivation.lib.mkSbtDerivation {
        inherit pkgs;
        overrides.sbt = pkgs.sbt.override { jre = pkgs.jdk25; };

        pname = "lambdalattice-jupyter-kernel";
        version = "0.1.0";
        # Gezi's directory without the files no sbt task reads: this directory of
        # Nix modules, the README and Gezi's flake, so that editing them does not
        # rebuild the jars, and the monorepo's .gitrepo, which the subrepo does not
        # have, so that the jars are the same derivation from either flake.
        src = lib.fileset.toSource {
          root = ../.;
          fileset = lib.fileset.difference ../. (
            lib.fileset.unions [
              ./.
              ../README.md
              ../flake.nix
              (lib.fileset.maybeMissing ../flake.lock)
              (lib.fileset.maybeMissing ../.gitrepo)
            ]
          );
        };

        depsSha256 = "sha256-LSd/JFIsjH6yNo5XAibGEr0/ttZJZyjz6jpQQOJGkEM=";
        depsWarmupCommand = ''
          sbt --client "jupyter-kernel/jupyterKernelInstall ${entryDirectory}"
          sbt --client shutdown
        '';
        overrideDepsAttrs = final: previous: {
          preBuild = setUpSbt;
          # sbt 2 keeps its disk cache of task results, compiled classes among them, and
          # its server's socket under the global base, which sbt-derivation puts in the
          # directory it packs (measured 2026-11-13: .sbtboot/cache/v2, 24 MB, and
          # .sbtboot/server). Neither is a dependency, and the compiled classes are no
          # download, so they are removed before the packing.
          postBuild = ''
            rm -r "$SBT_DEPS/project/.sbtboot/cache" "$SBT_DEPS/project/.sbtboot/server"
          '';
        };

        buildPhase = ''
          runHook preBuild
          ${setUpSbt}
          sbt --client "jupyter-kernel/jupyterKernelInstall ${entryDirectory}"
          sbt --client shutdown
          runHook postBuild
        '';

        installPhase = ''
          runHook preInstall
          mkdir -p $out/share/jupyter $out/share/gezi
          cp -r target/jupyter/kernels $out/share/jupyter/
          # The knowledge files entries import, off the variable gezi, the name of
          # the directory that holds both them and the entry's directory
          # (EntryData.read; lambdaJitTree below).
          cp -r corpora $out/share/gezi/
          substituteInPlace $out/share/jupyter/kernels/lambdalattice/kernel.json \
            --replace-fail "$PWD/target/jupyter" "$out/share/jupyter" \
            --replace-fail '"java"' '"${jdk}/bin/java"'
          runHook postInstall
        '';
      };

      # sbt's home and JVM inside the sandbox: the home is the build's temporary
      # directory, since the sandbox's HOME does not exist, and the JVM options are the
      # heap, stack, code cache and collector gezi/CONTRIBUTING.md starts sbt with,
      # its processor count limited to the cores Nix gives the build.
      setUpSbt = ''
        export HOME="$TMPDIR"
        export SBT_OPTS="-Xms64m -Xmx1200m -Xss4M -XX:ReservedCodeCacheSize=128m -XX:+UseZGC -XX:ActiveProcessorCount=$NIX_BUILD_CORES ''${SBT_OPTS:-}"
      '';

      # The tree an entry is read in, copied to the image's root: /gezi, the visible
      # subtree of the entry's reading (EntryData.read takes the entry directory's
      # parent), holding `corpora`, a symbolic link to the kernel's copy, which the tree's
      # reader follows (gezi.directorysugar.DirectoryTree reads with
      # Files.isDirectory and Files.list), the entry directory, empty in the base
      # image and holding the entry's file in an entry's image, and REVISION, the commit
      # the image was built from (a file without the .lambdalattice extension, which the
      # tree's reader skips).
      # FIXME: the standard place of the revision is the OCI annotation https://github.com/Atry/private-overlay/issues/2020
      # org.opencontainers.image.revision in the image config's Labels (with
      # org.opencontainers.image.source), but devenv's container module builds
      # nix2container's config from Entrypoint, User, WorkingDir, Env and Cmd only
      # (dev/devenv/src/modules/containers.nix, mkDerivation), with no option for labels.
      # The label waits on a `labels` option there, which gezi/flake.nix's pin of
      # github:Atry/devenv would also need, so the patch would have to be pushed to that
      # public repository, which is the user's decision; until then the revision is this
      # file.
      lambdaJitTree = name: entryFile:
        pkgs.runCommand "gezi-tree-${name}" { } ''
          mkdir -p $out/gezi/entry
          ln -s ${kernel}/share/gezi/corpora $out/gezi/corpora
          ${lib.optionalString (entryFile != null) "cp ${entryFile} $out/gezi/entry/entry.lambdalattice"}
          printf '%s\n' ${lib.escapeShellArgs [ "revision ${revision}" "repository gezi" ]} > $out/gezi/REVISION
        '';

      # The commit of the flake that builds the image; a tree with uncommitted changes
      # has only its dirty revision.
      revision = self.rev or self.dirtyRev;

      # The in-tree entries written as data, by the rule of project/EntryProjects.scala
      # (`writtenAsData`): a directory contest-entries-<player> that holds an
      # entry.lambdalattice and no Scala of its own.
      dataEntries = lib.pipe (builtins.readDir ../.) [
        (lib.filterAttrs (name: type: type == "directory" && lib.hasPrefix "contest-entries-" name))
        builtins.attrNames
        (builtins.filter (name: builtins.pathExists (../. + "/${name}/entry.lambdalattice")
          && !builtins.pathExists (../. + "/${name}/src/main/scala")))
        (map (name: lib.removePrefix "contest-entries-" name))
      ];

      python = pkgs.python3.withPackages (pythonPackages: [ pythonPackages.jupyter-console pythonPackages.notebook ]);

      # Jupyter's configuration, on JUPYTER_CONFIG_PATH: the kernel `jupyter console`
      # starts when no `--kernel` is given is lambdalattice's, not Python's.
      jupyterConfiguration = pkgs.writeTextDir "etc/jupyter/jupyter_console_config.json" (builtins.toJSON {
        ZMQTerminalIPythonApp.kernel_name = "lambdalattice";
      });

      shell = config.devenv.shells.gezi-jupyter;
    in
    {
      # The job's environment is these variables, whichever flake imports the module.
      # The monorepo's dev partition (modules/dev.nix) imports nix-ml-ops's nixLd and
      # ldFallbackManylinux, which give every job NIX_LD, LD_AUDIT and GLIBC_TUNABLES and
      # a fallback directory of manylinux libraries for binaries built outside Nix; the
      # image runs no such binary, the directory's closure holds gcc and systemd, 337 MB
      # (measured 2026-11-13), and gezi/flake.nix imports neither module, so the
      # image would differ between the two flakes.
      ml-ops.jobs.gezi-jupyter.environmentVariables = lib.mkForce {
        JUPYTER_PATH = "${kernel}/share/jupyter";
        JUPYTER_CONFIG_PATH = "${jupyterConfiguration}/etc/jupyter";
      };
      ml-ops.jobs.gezi-jupyter.devenvShellModule = devenvShell:
        let
          # devenv's entrypoint, which loads the shell's environment and runs its
          # arguments, taken from the container `shell` that devenv defines and nothing
          # here builds (a container's own default would refer to itself).
          shellEntrypoint = devenvShell.config.containers.shell.entrypoint;
          # A container of the image named `name` and tagged `tag`: the shell's closure
          # in the first layer, the same in every image, and the tree of /gezi in
          # the next. devenv's Cmd is the one word `startupCommand`, so the
          # entrypoint ends with `jupyter` and the command is its subcommand.
          container = name: tag: tree: {
            inherit name;
            version = tag;
            entrypoint = shellEntrypoint ++ [ "jupyter" ];
            startupCommand = "console";
            # devenv copies the flake's whole source into the image's home by default.
            copyToRoot = pkgs.emptyDirectory;
            layers = lib.mkBefore [
              { deps = shellEntrypoint ++ [ jupyterConfiguration ]; }
              { copyToRoot = [ tree ]; }
            ];
          };
        in
        {
          # The JDK is not among the packages: kernel.json names its java by its store
          # path, and devenv's profile links every output of a package, which for the JDK
          # brings its debug output and through it the JDK's source, 1.1 GB together
          # (measured 2026-11-13). No compiler is needed either, so the shell's stdenv is
          # the one without a C compiler (gcc and binutils, 318 MB).
          stdenv = pkgs.stdenvNoCC;
          packages = [ python ];
          containers =
            {
              processes = container "gezi-jupyter-base" "latest" (lambdaJitTree "base" null);
            }
            // lib.genAttrs dataEntries (player:
              container "gezi-jupyter" player
                (lambdaJitTree player (../. + "/contest-entries-${player}/entry.lambdalattice")));
        };

      packages =
        {
          lambdalattice-jupyter-kernel = kernel;
          gezi-jupyter-base = shell.containers.processes.derivation;
        }
        // lib.listToAttrs (map
          (player: lib.nameValuePair "gezi-jupyter-${player}" shell.containers.${player}.derivation)
          dataEntries);
    };
}
