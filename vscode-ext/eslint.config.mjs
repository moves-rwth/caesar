import eslint from '@eslint/js';
import tseslint from 'typescript-eslint';

export default tseslint.config(
    eslint.configs.recommended,
    ...tseslint.configs.recommendedTypeChecked,
    ...tseslint.configs.stylistic,
    {
        "languageOptions": {
            "parserOptions": {
                "project": "./tsconfig.json",
                tsconfigRootDir: import.meta.dirname,
                "ecmaVersion": 6,
                "sourceType": "module"
            }
        },
        "rules": {
            "@typescript-eslint/naming-convention": [
                "warn",
                {
                    "selector": "import",
                    "format": [
                        "camelCase",
                        "PascalCase"
                    ]
                },
            ],
            "@typescript-eslint/no-unused-vars": [
                "error",
                {
                    "destructuredArrayIgnorePattern": "^_"
                }
            ],
            "@typescript-eslint/semi": "warn",
            "curly": "warn",
            "eqeqeq": "warn",
            "no-throw-literal": "warn",
            "semi": "off",
            "@typescript-eslint/no-floating-promises": "error",
            "@typescript-eslint/no-explicit-any": "off",
            "@typescript-eslint/no-unsafe-assignment": "off"
        },
    }, {
    ignores: [
        "eslint.config.mjs",
        ".vscode-text.mjs",
        "out/",
        ".vscode-test.mjs"
    ]
});