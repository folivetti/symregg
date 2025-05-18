from symregg import symregg_run, SymRegg
import pandas as pd

output = symregg_run("test/data.csv", 100, "BestFirst", 10,  "add,sub,mul,div,log", "MSE", 50, 2, -1, 1,  False, "", "")

print(output)

print("Check PySymRegg")
df = pd.read_csv("test/data.csv")
Z = df.values
X = Z[:,:-1]
y = Z[:,-1]

reg = SymRegg(100, "BestFirst", 10, "add,sub,mul,div,log", "MSE", 50, 2, -1, 1, False, "", "")
reg.fit(X, y)
print(reg.score(X, y))


reg.fit_mvsr([X,X],[y,y])
print(reg.predict_mvsr(X,0))
print(reg.predict_mvsr(X,1))
print(reg.results)


reg = SymRegg(100, "BestFirst", 10, "add,sub,mul,div,log", "MSE", 50, 2, -1, 1, True, "", "")
reg.fit(X, y)
print(reg.results)
