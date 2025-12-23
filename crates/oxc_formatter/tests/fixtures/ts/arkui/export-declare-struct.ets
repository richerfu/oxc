// @keepTs
// @ts-nocheck
import { AuthResult } from "../i/m";
@Component
export declare struct v3 {
  authPageController: w3 | null;
  private controller;
  private url;
  private authPageParams;
  private timerId;
  private forceSetNetworkAvailable;
  @State
  progress: number;
  private hasBack;
  aboutToAppear(): void;
  aboutToDisappear(): void;
  private loadAuthUrl;
  private safeLoadUrl;
  build(): void;
  parseAuthResult(url: string): boolean;
  authFail(code: number, info: string): void;
  cancel(): void;
  back: (params: AuthResult) => void;
}
export declare class w3 {
  private j2;
  private f2;
  e2(y3: v3): void;
  cancelAuth(): void;
  private back;
}

