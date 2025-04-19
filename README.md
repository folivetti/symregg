# PySymRegg - Python bindings for SymRegg

A Python package for symbolic regression using e-graphs. PySymRegg is built on top of the SymRegg algorithm and provides a scikit-learn compatible API for symbolic regression tasks.

More info [here](https://github.com/folivetti/srtree/blob/main/apps/symregg/README.md)

## Installation

```bash
pip install pysymregg
```

## Features

- Scikit-learn compatible API with `fit()` and `predict()` methods
- Support for multiple optimization algorithms
- Flexible function set selection
- Various loss functions for different problem types
- Parameter optimization with multiple restarts
- Ability to save and load e-graphs

## Usage

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
from pysymregg import PySymRegg

# Split data
X_train, X_test, y_train, y_test = train_test_split(X, y, test_size=0.2)

# Create and fit model
model = PySymRegg(gen=150, optIter=100)
model.fit(X_train, y_train)

# Evaluate on test set
y_pred = model.predict(X_test)
mse = mean_squared_error(y_test, y_pred)
print(f"Test MSE: {mse}")
```

## Parameters

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
| `split` | int | 1 | Data splitting ratio for validation |
| `dumpTo` | str | "" | Filename to save the final e-graph |
| `loadFrom` | str | "" | Filename to load an e-graph to resume search |

## Available Functions

The following functions can be used in the `nonterminals` parameter:

- Basic operations: `add`, `sub`, `mul`, `div`
- Powers: `power`, `powerabs`, `square`, `cube`
- Roots: `sqrt`, `sqrtabs`, `cbrt`
- Trigonometric: `sin`, `cos`, `tan`, `asin`, `acos`, `atan`
- Hyperbolic: `sinh`, `cosh`, `tanh`, `asinh`, `acosh`, `atanh`
- Others: `abs`, `log`, `logabs`, `exp`, `recip`, `aq` (analytical quotient)

## Methods

- `fit(X, y)`: Fits the symbolic regression model
- `predict(X)`: Generates predictions using the best model
- `score(X, y)`: Computes R² score of the best model
- `evaluate_best_model(X)`: Evaluates the best model on the given data
- `evaluate_model(ix, X)`: Evaluates the model with index `ix` on the given data

## Results

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
