(function (root) {
  "use strict";

  const clamp = (value, low, high) => Math.max(low, Math.min(high, value));

  class SomaSceneRenderer {
    constructor(canvas) {
      this.canvas = canvas;
      this.context = canvas.getContext("2d", { alpha: false });
      this.hitTargets = [];
      this.lastStats = { selected: 0, renderVisible: 0, presented: 0 };
      this.colors = {};
      this.refreshColors();
    }

    refreshColors() {
      const styles = getComputedStyle(document.documentElement);
      const read = (name, fallback) => styles.getPropertyValue(name).trim() || fallback;
      this.colors = {
        ground: read("--ground", "#11171a"),
        line: read("--line", "#354149"),
        lineStrong: read("--line-strong", "#56666f"),
        inkFaint: read("--ink-faint", "#77858a"),
        primary: read("--primary", "#5bd4df"),
        sibling: read("--sibling", "#e3c26c"),
        ride: read("--ride", "#69cb8e"),
        found: read("--found", "#e26857"),
        boundary: read("--boundary-incidence", "#b9a875"),
        dependency: read("--dependency-incidence", "#61717a"),
        transport: read("--transport-incidence", "#69cb8e"),
        exposed: read("--exposed", "#e26857"),
      };
    }

    resize() {
      const bounds = this.canvas.getBoundingClientRect();
      const ratio = Math.min(2, window.devicePixelRatio || 1);
      const width = Math.max(1, Math.round(bounds.width * ratio));
      const height = Math.max(1, Math.round(bounds.height * ratio));
      if (this.canvas.width !== width || this.canvas.height !== height) {
        this.canvas.width = width;
        this.canvas.height = height;
      }
      this.context.setTransform(ratio, 0, 0, ratio, 0, 0);
      return { width: bounds.width, height: bounds.height, ratio };
    }

    project(point, viewport, camera) {
      const cameraX = ((point[0] << 1) + point[2]) >> 1;
      const cameraY = ((point[1] << 1) - point[2]) >> 1;
      const shortSide = Math.min(viewport.width, viewport.height);
      const scale = shortSide / (camera.orthoScale || 10000);
      return {
        x: viewport.x + viewport.width / 2 + cameraX * scale,
        y: viewport.y + viewport.height / 2 - cameraY * scale,
        depth: point[2],
        scale,
      };
    }

    roleColor(role) {
      const roles = {
        primary: this.colors.primary,
        sibling: this.colors.sibling,
        ride: this.colors.ride,
        found: this.colors.found,
        quiet: this.colors.lineStrong,
        grid: this.colors.line,
        "sheet-h2": this.colors.primary,
        "sheet-f3": this.colors.sibling,
        "axis-k": this.colors.ride,
        "boundary-incidence": this.colors.boundary,
        "dependency-incidence": this.colors.dependency,
        "transport-incidence": this.colors.transport,
        exposed: this.colors.exposed,
        open: this.colors.inkFaint,
      };
      return roles[role] || this.colors.inkFaint;
    }

    render(entries, camera) {
      const size = this.resize();
      const context = this.context;
      context.save();
      context.clearRect(0, 0, size.width, size.height);
      context.fillStyle = this.colors.ground;
      context.fillRect(0, 0, size.width, size.height);
      this.hitTargets = [];
      this.lastStats = { selected: 0, renderVisible: 0, presented: 0 };

      for (let index = 0; index < entries.length; index += 1) {
        const entry = entries[index];
        const viewport = entry.viewport;
        context.save();
        context.beginPath();
        context.rect(viewport.x, viewport.y, viewport.width, viewport.height);
        context.clip();
        this.drawReferencePlane(viewport);
        const stats = this.drawScene(entry.scene, viewport, entry.camera || camera, index);
        this.lastStats.selected += stats.selected;
        this.lastStats.renderVisible += stats.renderVisible;
        this.lastStats.presented += stats.presented;
        context.restore();
        if (index > 0) {
          context.strokeStyle = this.colors.lineStrong;
          context.lineWidth = 1;
          context.beginPath();
          context.moveTo(viewport.x + 0.5, viewport.y + 12);
          context.lineTo(viewport.x + 0.5, viewport.y + viewport.height - 12);
          context.stroke();
        }
      }
      context.restore();
    }

    drawReferencePlane(viewport) {
      const context = this.context;
      context.strokeStyle = this.colors.line;
      context.globalAlpha = 0.38;
      context.lineWidth = 1;
      for (let step = 1; step < 4; step += 1) {
        const y = viewport.y + viewport.height * step / 4;
        context.beginPath();
        context.moveTo(viewport.x + 12, y + 0.5);
        context.lineTo(viewport.x + viewport.width - 12, y + 0.5);
        context.stroke();
      }
      context.globalAlpha = 1;
    }

    drawScene(scene, viewport, camera, sceneIndex) {
      if (!scene) return { selected: 0, renderVisible: 0, presented: 0 };
      const projected = [];
      for (const item of scene.primitives) {
        const points = item.points.map((point) => this.project(point, viewport, camera));
        if (points.some((point) => !point)) continue;
        projected.push({ item, points, depth: points.reduce((sum, point) => sum + point.depth, 0) });
      }
      projected.sort((a, b) => b.depth - a.depth || a.item.id.localeCompare(b.item.id));
      for (const entry of projected) this.drawPrimitive(entry, sceneIndex);
      const presented = projected.filter((entry) => {
        const xs = entry.points.map((point) => point.x);
        const ys = entry.points.map((point) => point.y);
        return Math.min(...xs) <= viewport.x + viewport.width && Math.max(...xs) >= viewport.x &&
          Math.min(...ys) <= viewport.y + viewport.height && Math.max(...ys) >= viewport.y;
      }).length;
      return { selected: scene.primitives.length, renderVisible: projected.length, presented };
    }

    drawPrimitive(entry, sceneIndex) {
      const { item, points } = entry;
      const context = this.context;
      const color = this.roleColor(item.role);
      context.save();
      context.strokeStyle = color;
      context.fillStyle = color;
      context.globalAlpha = item.role === "grid" ? 0.3 : item.role === "quiet" ? 0.42 : 0.9;
      context.lineWidth = item.width || 1;
      context.setLineDash(item.dash || []);
      context.lineCap = "round";
      context.lineJoin = "round";

      if (item.kind === "label") {
        const text = String(item.metadata?.label || "");
        context.font = "11px SFMono-Regular, Consolas, Liberation Mono, monospace";
        context.textAlign = item.align === "center" ? "center" : item.align === "right" ? "right" : "left";
        context.textBaseline = "middle";
        context.globalAlpha = item.role === "quiet" ? 0.68 : 0.92;
        context.fillText(text, points[0].x, points[0].y);
        const width = context.measureText(text).width;
        const centerX = context.textAlign === "center" ? points[0].x : context.textAlign === "right" ? points[0].x - width / 2 : points[0].x + width / 2;
        this.hitTargets.push({ x: centerX, y: points[0].y, radius: Math.max(8, Math.min(28, width / 2)), item, sceneIndex });
      } else if (item.kind === "point") {
        const radius = clamp((item.radius || 3) * (0.65 + points[0].scale / 180), 1.5, 7);
        const side = Math.max(2, Math.round(radius * 2));
        context.fillRect(Math.round(points[0].x - side / 2), Math.round(points[0].y - side / 2), side, side);
        this.hitTargets.push({ x: points[0].x, y: points[0].y, radius: Math.max(8, radius + 4), item, sceneIndex });
      } else if (item.kind === "polygon") {
        context.beginPath();
        context.moveTo(points[0].x, points[0].y);
        for (let index = 1; index < points.length; index += 1) context.lineTo(points[index].x, points[index].y);
        context.closePath();
        context.globalAlpha *= 0.16;
        context.fill();
        context.globalAlpha *= 4.5;
        context.stroke();
        const centroid = points.reduce((sum, point) => ({ x: sum.x + point.x / points.length, y: sum.y + point.y / points.length }), { x: 0, y: 0 });
        this.hitTargets.push({ x: centroid.x, y: centroid.y, radius: 10, item, sceneIndex });
      } else {
        context.beginPath();
        context.moveTo(points[0].x, points[0].y);
        if (item.curve && points.length === 2) {
          const midX = (points[0].x + points[1].x) / 2;
          const midY = (points[0].y + points[1].y) / 2 - Math.abs(points[1].x - points[0].x) * item.curve;
          context.quadraticCurveTo(midX, midY, points[1].x, points[1].y);
        } else {
          for (let index = 1; index < points.length; index += 1) context.lineTo(points[index].x, points[index].y);
        }
        context.stroke();
        const midpoint = points[Math.floor(points.length / 2)];
        this.hitTargets.push({ x: midpoint.x, y: midpoint.y, radius: 7 + (item.width || 1), item, sceneIndex });
      }
      context.restore();
    }

    pick(clientX, clientY) {
      const bounds = this.canvas.getBoundingClientRect();
      const x = clientX - bounds.left;
      const y = clientY - bounds.top;
      let closest = null;
      for (const target of this.hitTargets) {
        const deltaX = target.x - x;
        const deltaY = target.y - y;
        const distanceSquared = deltaX * deltaX + deltaY * deltaY;
        const radiusSquared = target.radius * target.radius;
        if (distanceSquared <= radiusSquared && (!closest || distanceSquared < closest.distanceSquared)) {
          closest = { ...target, distanceSquared };
        }
      }
      return closest;
    }
  }

  root.SomaSceneRenderer = SomaSceneRenderer;
})(typeof globalThis !== "undefined" ? globalThis : this);
