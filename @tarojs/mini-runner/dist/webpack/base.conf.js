"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
const path = require("path");
const Chain = require("webpack-chain");
exports.default = (appPath) => {
    const chain = new Chain();
    chain.merge({
        resolve: {
            extensions: ['.js', '.jsx', '.ts', '.tsx'],
            mainFields: ['browser', 'module', 'main'],
            symlinks: true,
            modules: [
                path.join(appPath, 'node_modules'),
                'node_modules'
            ]
        },
        resolveLoader: {
            modules: [
                'node_modules'
            ]
        }
    });
    return chain;
};
