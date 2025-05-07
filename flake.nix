{
  description = "Semantic Cut Elimination mechanised proofs and documents";
  inputs = {
    nixpkgs.url = github:NixOS/nixpkgs/nixos-24.11;
    flake-utils.url = github:numtide/flake-utils;
  };
  outputs = { self, nixpkgs, flake-utils }:
    with flake-utils.lib;
    eachSystem allSystems (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        tex = pkgs.texlive.combine {
          inherit (pkgs.texlive)
            scheme-basic
            latexmk cmll mathpartir xypic todonotes mathtools
            xifthen ifmtarg polytable lazylist etoolbox environ
            newunicodechar
            mathcommand foreign xpunctuate cleveref
            fdsymbol stmaryrd
            vntex enumitem
            parskip multirow ec metafont
            cclicenses microtype thmtools helvetic
          ;
        };

        agda = pkgs.agda.withPackages
          (ps: [ (ps.standard-library.overrideAttrs (oldAttrs: {
            version = "2.2";
            src = pkgs.fetchFromGitHub {
              repo = "agda-stdlib";
              owner = "agda";
              rev = "v2.2";
              hash = "sha256-/Fy5EOSbVNXt6Jq0yKSnlNPW4SYfn+eCTAYFnMZrbR0=";
              #hash = "sha256-TjGvY3eqpF+DDwatT7A78flyPcTkcLHQ1xcg+MKgCoE=";
            };
          })) ]);
      in rec {
        packages = {
          html-doc = pkgs.stdenvNoCC.mkDerivation rec {
            name = "semantic-cut-elimination";
            src = self;
            buildInputs = [ agda ];
            phases = ["unpackPhase" "buildPhase" "installPhase"];
            buildPhase = ''
mkdir -p html;
agda --html --html-dir=html src/index.agda
'';
            installPhase = ''
mkdir -p $out;
cp html/* $out/;
'';
          };
          paper = pkgs.stdenvNoCC.mkDerivation rec {
            name = "Paper on Semantic Cut Elimination for Multiplicative Additive System Virtual";
            src = self;
            buildInputs = [ pkgs.coreutils tex agda pkgs.gnumake pkgs.which pkgs.bash ];
            phases = ["unpackPhase" "buildPhase" "installPhase"];
            buildPhase = ''
export PATH="${pkgs.lib.makeBinPath buildInputs}";
export DIR=$(pwd);
mkdir -p "$DIR"/doc/.cache/texmf-var;
cd doc/
env TEXMFHOME="$DIR/doc/.cache" TEXMFVAR="$DIR/doc/.cache/texmf-var" make AGDA=agda
'';
            installPhase = ''
mkdir -p $out;
cp paper.pdf $out/
'';
          };
          journal-paper = pkgs.stdenvNoCC.mkDerivation rec {
            name = "Paper on Semantic Cut Elimination for Deep Inference (Journal Version)";
            src = self;
            buildInputs = [ pkgs.coreutils tex agda pkgs.gnumake pkgs.which pkgs.bash ];
            phases = ["unpackPhase" "buildPhase" "installPhase"];
            buildPhase = ''
export PATH="${pkgs.lib.makeBinPath buildInputs}";
export DIR=$(pwd);
mkdir -p "$DIR"/doc/.cache/texmf-var;
cd journal-version
env TEXMFHOME="$DIR/doc/.cache" TEXMFVAR="$DIR/doc/.cache/texmf-var" make AGDA=agda
'';
            installPhase = ''
mkdir -p $out;
cp paper.pdf $out/
'';
          };
        };
        defaultPackage = packages.html-doc;

        devShells.default = pkgs.mkShell {
          inputsFrom = builtins.attrValues packages;
          # buildInputs = devPackages ++ [
          #   pkgs.rsync
          # ];
        };

      });
}
