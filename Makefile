
objects = dfy/Util.cs dfy/SAT.cs dfy/CNF.cs dfy/Set.cs dfy/Map.cs dfy/Seq.cs
all: $(objects)

dfy/%.cs: dfy/%.dfy
	"/usr/bin/dotnet" "/home/john/.vscode-server/extensions/dafny-lang.ide-vscode-3.2.1/out/resources/4.3.0/github/dafny/Dafny.dll" "translate" "cs" "--output:$@" "$<"
