// Test file for experiments.ts
import { Calculator, greet, fibonacci } from './experiments';

describe('Calculator', () => {
  let calculator: Calculator;

  beforeEach(() => {
    calculator = new Calculator();
  });

  test('should add two numbers correctly', () => {
    expect(calculator.add(2, 3)).toBe(5);
    expect(calculator.add(-1, 1)).toBe(0);
    expect(calculator.add(0, 0)).toBe(0);
  });

  test('should subtract two numbers correctly', () => {
    expect(calculator.subtract(5, 3)).toBe(2);
    expect(calculator.subtract(1, 1)).toBe(0);
    expect(calculator.subtract(0, 5)).toBe(-5);
  });

  test('should multiply two numbers correctly', () => {
    expect(calculator.multiply(2, 3)).toBe(6);
    expect(calculator.multiply(-2, 3)).toBe(-6);
    expect(calculator.multiply(0, 5)).toBe(0);
  });

  test('should divide two numbers correctly', () => {
    expect(calculator.divide(6, 2)).toBe(3);
    expect(calculator.divide(5, 2)).toBe(2.5);
    expect(calculator.divide(-6, 2)).toBe(-3);
  });

  test('should throw error when dividing by zero', () => {
    expect(() => calculator.divide(5, 0)).toThrow("Division by zero is not allowed");
  });
});

describe('greet function', () => {
  test('should return greeting with name', () => {
    expect(greet('World')).toBe('Hello, World!');
    expect(greet('TypeScript')).toBe('Hello, TypeScript!');
    expect(greet('')).toBe('Hello, !');
  });
});

describe('fibonacci function', () => {
  test('should return correct fibonacci numbers', () => {
    expect(fibonacci(0)).toBe(0);
    expect(fibonacci(1)).toBe(1);
    expect(fibonacci(2)).toBe(1);
    expect(fibonacci(3)).toBe(2);
    expect(fibonacci(4)).toBe(3);
    expect(fibonacci(5)).toBe(5);
    expect(fibonacci(6)).toBe(8);
  });
});
