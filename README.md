Exercises from the book '[Programing Language Foundations in Agda](https://plfa.github.io/)'.

## Environment Setup

This is tested on Ubuntu 18.04 using [Haskell Tool Stack](https://docs.haskellstack.org/en/stable/install_and_upgrade/).

Install a few prerequisites:
```
sudo apt install emacs libncurses5-dev
```
I install Agda in a specific project:

```
stack new agda
cd agda
```

If we just try to install Agda, we get some errors regarding missing dependencies. Fortunalety, the Stack error messages describe what has to be added to the `extra-deps` section in the `stack.yaml` file. This is my final configuration for `extra-deps`:

```
extra-deps:
- data-hash-0.2.0.1@sha256:0277d99cb8b535ecc375c59e55f1c91faab966d9167a946ef18445dd468ba727,1135
- equivalence-0.3.5@sha256:aedbd070b7ab5e58dd1678cd85607bc33cb9ff62331c1fa098ca45063b3072db,1626
- geniplate-mirror-0.7.7@sha256:6a698c1bcec25f4866999001c4de30049d4f8f00ec83f8930cda2f767489c637,1106
- STMonadTrans-0.4.4@sha256:437eec4fdf5f56e9cd4360e08ed7f8f9f5f02ff3f1d634a14dbc71e890035387,1946
```

Now, Agda installation should proceed without errors:

```
stack install alex happy Agda
agda-mode setup && agda-mode compile
```

I don't usually work with emacs, so after running the above commands my .emacs file is pretty simple:

```
$ cat ~/.emacs
(load-file (let ((coding-system-for-read 'utf-8))
                (shell-command-to-string "agda-mode locate")))
```

`agda-stdlib` is also required. I've installed it in my home directory:
```
cd $HOME
wget -O agda-stdlib.tar https://github.com/agda/agda-stdlib/archive/v1.3.tar.gz
tar xf agda-stdlib.tar

mkdir $HOME/.agda
echo "$HOME/agda-stdlib-1.3/standard-library.agda-lib" > .agda/libraries
echo "standard-library" > .agda/defaults
```

That's all. Now, run emacs and start editing Agda files.
