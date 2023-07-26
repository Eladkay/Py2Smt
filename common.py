class Py2SmtException(Exception):
    def __init__(self, s: str):
        super().__init__(s)
