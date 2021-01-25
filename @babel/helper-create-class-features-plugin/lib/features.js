"use strict";

Object.defineProperty(exports, "__esModule", {
  value: true
});
exports.enableFeature = enableFeature;
exports.isLoose = isLoose;
exports.verifyUsedFeatures = verifyUsedFeatures;
exports.FEATURES = void 0;

var _decorators = require("./decorators");

const FEATURES = Object.freeze({
  fields: 1 << 1,
  privateMethods: 1 << 2,
  decorators: 1 << 3,
  privateIn: 1 << 4
});
exports.FEATURES = FEATURES;
const featuresKey = "@babel/plugin-class-features/featuresKey";
const looseKey = "@babel/plugin-class-features/looseKey";

function enableFeature(file, feature, loose) {
  if (!hasFeature(file, feature)) {
    file.set(featuresKey, file.get(featuresKey) | feature);
    if (loose) file.set(looseKey, file.get(looseKey) | feature);
  }

  if (hasFeature(file, FEATURES.fields) && hasFeature(file, FEATURES.privateMethods) && isLoose(file, FEATURES.fields) !== isLoose(file, FEATURES.privateMethods)) {
    throw new Error("'loose' mode configuration must be the same for both @babel/plugin-proposal-class-properties " + "and @babel/plugin-proposal-private-methods");
  }

  if (hasFeature(file, FEATURES.fields) && hasFeature(file, FEATURES.privateIn) && isLoose(file, FEATURES.fields) !== isLoose(file, FEATURES.privateIn)) {
    throw new Error("'loose' mode configuration must be the same for both @babel/plugin-proposal-class-properties " + "and @babel/plugin-proposal-private-property-in-object");
  }

  if (hasFeature(file, FEATURES.privateMethods) && hasFeature(file, FEATURES.privateIn) && isLoose(file, FEATURES.privateMethods) !== isLoose(file, FEATURES.privateIn)) {
    throw new Error("'loose' mode configuration must be the same for both @babel/plugin-proposal-private-methods " + "and @babel/plugin-proposal-private-property-in-object");
  }
}

function hasFeature(file, feature) {
  return !!(file.get(featuresKey) & feature);
}

function isLoose(file, feature) {
  return !!(file.get(looseKey) & feature);
}

function verifyUsedFeatures(path, file) {
  if ((0, _decorators.hasOwnDecorators)(path.node)) {
    if (!hasFeature(file, FEATURES.decorators)) {
      throw path.buildCodeFrameError("Decorators are not enabled." + "\nIf you are using " + '["@babel/plugin-proposal-decorators", { "legacy": true }], ' + 'make sure it comes *before* "@babel/plugin-proposal-class-properties" ' + "and enable loose mode, like so:\n" + '\t["@babel/plugin-proposal-decorators", { "legacy": true }]\n' + '\t["@babel/plugin-proposal-class-properties", { "loose": true }]');
    }

    if (path.isPrivate()) {
      throw path.buildCodeFrameError(`Private ${path.isClassMethod() ? "methods" : "fields"} in decorated classes are not supported yet.`);
    }
  }

  if (path.isPrivate() && path.isMethod()) {
    if (!hasFeature(file, FEATURES.privateMethods)) {
      throw path.buildCodeFrameError("Class private methods are not enabled.");
    }
  }

  if (path.isPrivateName() && path.parentPath.isBinaryExpression({
    operator: "in",
    left: path.node
  })) {
    if (!hasFeature(file, FEATURES.privateIn)) {
      throw path.buildCodeFrameError("Private property in checks are not enabled.");
    }
  }

  if (path.isProperty()) {
    if (!hasFeature(file, FEATURES.fields)) {
      throw path.buildCodeFrameError("Class fields are not enabled.");
    }
  }
}