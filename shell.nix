let 
    pkgs = import (
        fetchTarball "https://nixos.org/channels/nixos-22.11/nixexprs.tar.xz"
    ) {};
    jdk = pkgs.jdk11_headless;
in
    pkgs.mkShell {
        buildInputs = [
            jdk
            (pkgs.scala_2_12.override {
                jre = jdk;   
            })
            pkgs.sbt            
        ];

        shellHook = ''
          chmod +x ./tip;
        '';
    }
