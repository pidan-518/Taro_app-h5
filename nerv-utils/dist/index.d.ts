// Generated by dts-bundle v0.7.3

declare module 'nerv-utils' {
    export { default as nextTick } from 'nerv-utils/next-tick';
    export { default as shallowEqual } from 'nerv-utils/shallow-equal';
    export { SimpleMap, MapClass } from 'nerv-utils/simple-map';
    export * from 'nerv-utils/is';
    export * from 'nerv-utils/env';
    export function getPrototype(obj: any): any;
    export function isAttrAnEvent(attr: string): boolean;
    const extend: <S, F>(source: S, from: F) => S | (F & S);
    export { extend };
    export function clone<T>(obj: T): T | {};
}

declare module 'nerv-utils/next-tick' {
    const nextTick: (fn: any, ...args: any[]) => void;
    export default nextTick;
}

declare module 'nerv-utils/shallow-equal' {
    export default function shallowEqual(obj1: any, obj2: any): boolean;
}

declare module 'nerv-utils/simple-map' {
    export interface Cache<Key, Value> {
        k: Key;
        v: Value;
    }
    export class SimpleMap<Key, Value> {
        cache: Array<Cache<Key, Value>>;
        size: number;
        constructor();
        set(k: any, v: any): void;
        get(k: any): Value | undefined;
        has(k: any): boolean;
        delete(k: any): boolean;
        clear(): void;
    }
    export const MapClass: MapConstructor;
}

declare module 'nerv-utils/is' {
    export function isNumber(arg: any): arg is number;
    export const isSupportSVG: boolean;
    export function isString(arg: any): arg is string;
    export function isFunction(arg: any): arg is Function;
    export function isBoolean(arg: any): arg is true | false;
    export const isArray: (arg: any) => arg is any[];
    export function isObject(arg: any): arg is Object;
    export function isNative(Ctor: any): boolean;
    export function isUndefined(o: any): o is undefined;
    export function objectIs(x: any, y: any): boolean;
}

declare module 'nerv-utils/env' {
    export var global: any;
    export const isBrowser: boolean;
    export const doc: Document;
    export const UA: string | false;
    export const isMacSafari: boolean | "";
    export const isTaro: false;
    export const isIE9: boolean | "";
    export const isiOS: boolean | "";
}
