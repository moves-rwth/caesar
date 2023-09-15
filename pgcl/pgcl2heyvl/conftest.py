def pytest_addoption(parser):
    parser.addoption("--overwrite-golden",
                     action="store_true",
                     help="reset golden files benchmarks")
