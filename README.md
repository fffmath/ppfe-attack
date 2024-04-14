# GIFP

Code for the paper [“Partial prime factor exposure attacks on some RSA variants"](https://doi.org/10.1016/j.tcs.2024.114549).

## Introduction

This is a Python implementation of PPFE Attack based on [Joachim Vandersmissen's crypto-attacks](https://github.com/jvdsn/crypto-attacks) and [Mengce Zheng's Boneh_Durfee_Attack](https://github.com/MengceZheng/Boneh_Durfee_Attack).

## Requirements

- [SageMath](https://www.sagemath.org/) with Python 3.11.1. SageMath 9.8 is recommended.

  You can check your SageMath Python version using the following command:

```bash
$ sage -python --version
Python 3.11.1
```
Note: If your SageMath Python version is older than 3.11.1, some features in some scripts might not work.

## Usage
```bash
# sage -python attack1.py to run the code in Thm 4
sage -python attack1.py

# sage -python attack2.py to run the code in Thm 5
sage -python attack2.py

```

### Debug

You can enable debugging by setting `logging.basicConfig(filename='gifp.log', level=logging.DEBUG, format='%(asctime)s - %(levelname)s - %(message)s')` in your code.

### Note
It is important to note that there exist two root (-k, p+q-p0-q0) and (-k, p+q-p0-q0) in Theorem 4.

### Author

You can find more information on [my personal website](https://www.fffmath.com/).

### License

This script is released under the MIT License. See the [LICENSE](LICENSE) file for details.