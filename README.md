# SymRegg - Equality graph Assisted Search Technique for Equation Discovery (Symbolic Regression)

This repository provides a CLI and a Python package for SymRegg with a scikit-learn compatible API for symbolic regression.

A Python package for symbolic regression using e-graphs. PySymRegg is built on top of the SymRegg algorithm and provides a scikit-learn compatible API for symbolic regression tasks.

- [CLI version](#cli)
- [Python version](#python)

## CLI

### How to use 

```bash
SymRegg - symbolic regression with e-graphs.

Usage: egraphSearch (-d|--dataset INPUT-FILE) [-t|--test ARG] 
                    [-g|--generations GENS] (-a|--algorithm ALG)
                    (-s|--maxSize ARG) [-k|--folds ARG] 
                    [--trace] [--loss ARG] [--opt-iter ARG] 
                    [--opt-retries ARG] [--non-terminals ARG] [--dump-to ARG] 
                    [--load-from ARG]

  Symbolic Regression search algorithm exploiting the potentials of equality
  saturation and e-graphs.

Available options:
  -d,--dataset INPUT-FILE  CSV dataset.
  -t,--test ARG            test data (default: "")
  -g,--generations GENS    Number of generations. (default: 100)
  -a,--algorithm ALG       Algorithm.
  -s,--maxSize ARG         max-size.
  -k,--folds ARG           k-split ratio training-validation (default: 1)
  --trace                  print all evaluated expressions.
  --loss ARG       distribution of the data. (default: Gaussian)
  --opt-iter ARG           number of iterations in parameter optimization.
                           (default: 30)
  --opt-retries ARG        number of retries of parameter fitting. (default: 1)
  --non-terminals ARG      set of non-terminals to use in the search.
                           (default: "Add,Sub,Mul,Div,PowerAbs,Recip")
  --dump-to ARG            dump final e-graph to a file. (default: "")
  --load-from ARG          load initial e-graph from a file. (default: "")
  -h,--help                Show this help text
```

The dataset file must contain a header with each features name, and the `--dataset` and `--test` arguments can be accompanied by arguments separated by ':' following the format:

`filename.ext:start_row:end_row:target:features:ynoise`

where each ':' field is optional. The fields are:

- **start_row:end_row** is the range of the training rows (default 0:nrows-1).
   every other row not included in this range will be used as validation
- **target** is either the name of the  (if the datafile has headers) or the index
   of the target variable
- **features** is a comma separated list of names or indices to be used as
  input variables of the regression model.
- **ynoise** is either the name or the index of the noise / uncertainty information of the target.

Example of valid names: `dataset.csv`, `mydata.tsv`, `dataset.csv:20:100`, `dataset.tsv:20:100:price:m2,rooms,neighborhood`, `dataset.csv:::5:0,1,2`.

The format of the file will be determined by the extension (e.g., csv, tsv,...). 

### Installation

To install SymRegg you'll need:

- `libz`
- `libnlopt`
- `libgmp`
- `ghc-9.6.6` or higher
- `cabal`

### Method 1: PIP

Simply run:

```bash
pip install symregg 
```

under your Python environment.

### Method 2: Pre-compile binaries

Go to the [releases](https://github.com/folivetti/symregg/tags) page, download the eggp binary corresponding to your OS and rename it to `symregg`.

Note: Windows and OSX releases are untested, for Windows Mingw with libnlopt are required.

### Method 3: cabal

After installing the dependencies (e.g., `apt install libz libnlopt libgmp`), install [`ghcup`](https://www.haskell.org/ghcup/#)

For Linux, macOS, FreeBSD or WSL2:

```bash 
curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
```

For Windows, run the following in a PowerShell:

```bash
Set-ExecutionPolicy Bypass -Scope Process -Force;[System.Net.ServicePointManager]::SecurityProtocol = [System.Net.ServicePointManager]::SecurityProtocol -bor 3072; try { & ([ScriptBlock]::Create((Invoke-WebRequest https://www.haskell.org/ghcup/sh/bootstrap-haskell.ps1 -UseBasicParsing))) -Interactive -DisableCurl } catch { Write-Error $_ }
```

After the installation, run `ghcup tui` and install the latest `stack` or `cabal` together with `ghc-9.6.6` (select the items and press `i`).
To install `symregg` simply run:

```bash 
cabal install
```

## Python

### Installation

```bash
pip install pysymregg
```

### Features

- Scikit-learn compatible API with `fit()` and `predict()` methods
- Support for multiple optimization algorithms
- Flexible function set selection
- Various loss functions for different problem types
- Parameter optimization with multiple restarts
- Ability to save and load e-graphs

### Usage

### Basic Example

```python
from pysymregg import PySymRegg
import numpy as np

# Create sample data
X = np.linspace(-10, 10, 100).reshape(-1, 1)
y = 2 * X.ravel() + 3 * np.sin(X.ravel()) + np.random.normal(0, 1, 100)

# Create and fit the model
model = PySymRegg(gen=100, nonterminals="add,sub,mul,div,sin,cos")
model.fit(X, y)

# Make predictions
y_pred = model.predict(X)

# Examine the results
print(model.results)
```

### Integration with scikit-learn

```python
from sklearn.model_selection import train_test_split
from sklearn.metrics import mean_squared_error
from symregg import SymRegg

# Split data
X_train, X_test, y_train, y_test = train_test_split(X, y, test_size=0.2)

# Create and fit model
model = SymRegg(gen=150, optIter=100)
model.fit(X_train, y_train)

# Evaluate on test set
y_pred = model.predict(X_test)
mse = mean_squared_error(y_test, y_pred)
print(f"Test MSE: {mse}")
```

### Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `gen` | int | 100 | Number of generations to run |
| `alg` | str | "BestFirst" | Algorithm type: "BestFirst" or "OnlyRandom" |
| `maxSize` | int | 15 | Maximum allowed size for expressions (max 100) |
| `nonterminals` | str | "add,sub,mul,div" | Comma-separated list of allowed functions |
| `loss` | str | "MSE" | Loss function: "MSE", "Gaussian", "Bernoulli", or "Poisson" |
| `optIter` | int | 50 | Number of iterations for parameter optimization |
| `optRepeat` | int | 2 | Number of restarts for parameter optimization |
| `nParams` | int | -1 | Maximum number of parameters (-1 for unlimited) |
| `folds` | int | 1 | Data splitting ratio for validation |
| `trace` | bool | False | Whether to return all visited expressions instead of the Pareto front |
| `dumpTo` | str | "" | Filename to save the final e-graph |
| `loadFrom` | str | "" | Filename to load an e-graph to resume search |

### Available Functions

The following functions can be used in the `nonterminals` parameter:

- Basic operations: `add`, `sub`, `mul`, `div`
- Powers: `power`, `powerabs`, `square`, `cube`
- Roots: `sqrt`, `sqrtabs`, `cbrt`
- Trigonometric: `sin`, `cos`, `tan`, `asin`, `acos`, `atan`
- Hyperbolic: `sinh`, `cosh`, `tanh`, `asinh`, `acosh`, `atanh`
- Others: `abs`, `log`, `logabs`, `exp`, `recip`, `aq` (analytical quotient)

### Methods

- `fit(X, y, Xerr, yerr)`: Fits the symbolic regression model with optional uncertainty information for `X, y`.
- `fit_mvsr(Xs, ys, Xerrs, yerrs)`: Fits the symbolic regression model using multi-view SR where each argument is a list of numpy arrays describing multiple samples.
- `predict(X)`: Generates predictions using the best model
- `predict_mvsr(X, view)`: counter part of `predict` for multi-view. Must specify the view.
- `score(X, y)`: Computes R² score of the best model
- `evaluate_best_model(X)`: Evaluates the best model on the given data
- `evaluate_best_model_mvsr(X, view)`: Counterpart for multi-view. Must specify the view.
- `evaluate_model(ix, X)`: Evaluates the model with index `ix` on the given data
- `evaluate_model_mvsr(ix, X, view)`: Counterpart for multi-view. Must specify the view.

### Results

After fitting, the `results` attribute contains a pandas DataFrame with details about the discovered models, including:
- Mathematical expressions
- Model complexity
- Parameter values
- Error metrics
- NumPy-compatible expressions

## License

[LICENSE]

## Citation

If you use PySymRegg in your research, please cite:

TBD

## Acknowledgments

The bindings were created following the amazing example written by [wenkokke](https://github.com/wenkokke/example-haskell-wheel)

Fabricio Olivetti de Franca is supported by Conselho Nacional de Desenvolvimento Cient\'{i}fico e Tecnol\'{o}gico (CNPq) grant 301596/2022-0.

Gabriel Kronberger is supported by the Austrian Federal Ministry for Climate Action, Environment, Energy, Mobility, Innovation and Technology, the Federal Ministry for Labour and Economy, and the regional government of Upper Austria within the COMET project ProMetHeus (904919) supported by the Austrian Research Promotion Agency (FFG). 
