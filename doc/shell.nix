{ pkgs ? import <nixpkgs> { } }:
with pkgs;
mkShell {
  buildInputs = [
    (agda.withPackages (ps: [
      ps.standard-library
    ]))
    (pkgs.texlive.combine {
      inherit (pkgs.texlive) scheme-basic
        latexmk cmll mathpartir xypic todonotes;
    })
  ];
  shellHook = ''
    make .latexmkrc
  '';
}
