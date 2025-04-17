from pysymregg import pysymregg_run, PySymRegg
import pandas as pd

output = pysymregg_run("test/data.csv", 100, "BestFirst", 10,  "add,sub,mul,div,log", "MSE", 50, 2, -1, 1,  "", "")

print(output)

print("Check PySymRegg")
df = pd.read_csv("test/data.csv")
Z = df.values
X = Z[:,:-1]
y = Z[:,-1]

reg = PySymRegg(100, "BestFirst", 10, "add,sub,mul,div,log", "MSE", 50, 2, -1, 1, "", "")
reg.fit(X, y)
print(reg.score(X, y))
