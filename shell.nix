let 
  rien = import /home/frob/code/rien/rien.nix {
    packageName = "preposterous";
    packagePath = ./.;

    # Instead of using <nixpkgs>, use a lock-file to stick to
    # a particular `nixpkgs` commit.
    nixpkgsLock = ./nixpkgs.json;

    ghcVersion = "ghc822";

    overrides = rec {
      skipTests = [ "ghc-mod" "hpack" "llvm-hs-pretty" ];
      jailbreak = [ "cabal-helper" "ghc-mod" ];
      skipHaddock = justStaticExecutables;
      justStaticExecutables = [ 
        "brittany" 
        "hpack"
        "ghcid"
        "hpack"
      ];
    };
  };

in
  rien.shell {
    # Generate Hoogle documentation?
    wantHoogle = true;

    # Haskell dependencies
    deps = hsPkgs: with hsPkgs; [
      brittany
      ghc-mod
      cabal-helper
      hpack

      text
      bound
      prettyprinter
      lens
      deriving-compat

      llvm-hs-pure
      llvm-hs-pretty
      llvm-hs-typed
      # containers
      # logict
      # QuickCheck

      # hpack
      # ghcid
      # hlint
      # adjunctions
      # exceptions
      # hashable
      # hspec
      # lens
      # mtl
      # prettyprinter
      # prettyprinter-ansi-terminal
      # profunctors
      # safe
      # text
      # uniplate
      # unordered-containers
    ];

    # Optionally, also add sets of related packages that are
    # commonly used together.
    depSets = hsPkgs: with (rien.package-sets hsPkgs); [
      development-servers
    ];

    # Native dependencies
    nativeDeps = pkgs: with pkgs; [ 
      # z3 
      llvm_5
    ];
  }
