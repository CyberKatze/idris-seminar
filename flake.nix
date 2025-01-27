{  
  description = "Development environment with Nix flakes and direnv";  

  inputs = {  
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.05";  
    flake-utils.url = "github:numtide/flake-utils";  
  };  

  outputs = { self, nixpkgs, flake-utils }:  
    flake-utils.lib.eachDefaultSystem (system:  
      let  
        pkgs = import nixpkgs { inherit system; };  
        tex = pkgs.texlive.combine {
          inherit (pkgs.texlive) scheme-medium todonotes latexmk pgf biber koma-script biblatex blindtext nicematrix fontspec;
        };
      in rec{  
        devShell = pkgs.mkShell {  
          buildInputs = [  
            pkgs.idris2
            pkgs.idris2Packages.idris2Lsp
            tex
            pkgs.presenterm
          ];  
        };  

        packages = {

          document = pkgs.stdenvNoCC.mkDerivation rec {
            name = "
          latex-demo-document
          ";
            src = self;
            buildInputs = [ pkgs.coreutils tex ];
            phases = [
              "
          unpackPhase
          "
              "
          buildPhase
          "
              "
          installPhase
          "
            ];
            buildPhase = ''  
              export PATH="${pkgs.lib.makeBinPath buildInputs}";  
              cd report  
              mkdir -p .cache/texmf-var  
              env TEXMFHOME=.cache TEXMFVAR=.cache/texmf-var \
                SOURCE_DATE_EPOCH=${toString self.lastModified} \
                latexmk -interaction=nonstopmode -pdf -lualatex \
                -pretex="\pdfvariable suppressoptionalinfo 512\relax" \
                -usepretex main.tex  
            '';
            installPhase = ''
              mkdir -p $out
              cp main.pdf $out/
            '';
          };
        };
        defaultPackage = packages.document;
      }  
    );  
}
